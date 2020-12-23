%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :   17 (  24 expanded)
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

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k2_tarski(C,D)) = k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(A,B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_mcart_1)).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_26,B_27,C_28] : k2_zfmisc_1(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k2_tarski(k4_tarski(A_26,B_27),k4_tarski(A_26,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_5,B_6,B_27,C_7] : k2_zfmisc_1(k1_tarski(k4_tarski(A_5,B_6)),k2_tarski(B_27,C_7)) = k2_tarski(k4_tarski(k4_tarski(A_5,B_6),B_27),k3_mcart_1(A_5,B_6,C_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_126,plain,(
    ! [A_5,B_6,B_27,C_7] : k2_zfmisc_1(k1_tarski(k4_tarski(A_5,B_6)),k2_tarski(B_27,C_7)) = k2_tarski(k3_mcart_1(A_5,B_6,B_27),k3_mcart_1(A_5,B_6,C_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_26,C_28] : k2_zfmisc_1(k1_tarski(A_26),k2_tarski(C_28,C_28)) = k1_tarski(k4_tarski(A_26,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_129,plain,(
    ! [A_29,C_30] : k2_zfmisc_1(k1_tarski(A_29),k1_tarski(C_30)) = k1_tarski(k4_tarski(A_29,C_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_29,C_30,C_10] : k3_zfmisc_1(k1_tarski(A_29),k1_tarski(C_30),C_10) = k2_zfmisc_1(k1_tarski(k4_tarski(A_29,C_30)),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_12,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_148,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.31  
% 2.10/1.31  %Foreground sorts:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Background operators:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Foreground operators:
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.31  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.10/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.31  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.31  
% 2.44/1.32  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.44/1.32  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.44/1.32  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.32  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.44/1.32  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k2_tarski(C, D)) = k2_tarski(k3_mcart_1(A, B, C), k3_mcart_1(A, B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_mcart_1)).
% 2.44/1.32  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.32  tff(c_78, plain, (![A_26, B_27, C_28]: (k2_zfmisc_1(k1_tarski(A_26), k2_tarski(B_27, C_28))=k2_tarski(k4_tarski(A_26, B_27), k4_tarski(A_26, C_28)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.32  tff(c_112, plain, (![A_5, B_6, B_27, C_7]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_5, B_6)), k2_tarski(B_27, C_7))=k2_tarski(k4_tarski(k4_tarski(A_5, B_6), B_27), k3_mcart_1(A_5, B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 2.44/1.32  tff(c_126, plain, (![A_5, B_6, B_27, C_7]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_5, B_6)), k2_tarski(B_27, C_7))=k2_tarski(k3_mcart_1(A_5, B_6, B_27), k3_mcart_1(A_5, B_6, C_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 2.44/1.32  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.32  tff(c_97, plain, (![A_26, C_28]: (k2_zfmisc_1(k1_tarski(A_26), k2_tarski(C_28, C_28))=k1_tarski(k4_tarski(A_26, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 2.44/1.32  tff(c_129, plain, (![A_29, C_30]: (k2_zfmisc_1(k1_tarski(A_29), k1_tarski(C_30))=k1_tarski(k4_tarski(A_29, C_30)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_97])).
% 2.44/1.32  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.32  tff(c_138, plain, (![A_29, C_30, C_10]: (k3_zfmisc_1(k1_tarski(A_29), k1_tarski(C_30), C_10)=k2_zfmisc_1(k1_tarski(k4_tarski(A_29, C_30)), C_10))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 2.44/1.32  tff(c_12, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.32  tff(c_148, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 2.44/1.32  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_148])).
% 2.44/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  
% 2.44/1.32  Inference rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Ref     : 0
% 2.44/1.32  #Sup     : 120
% 2.44/1.32  #Fact    : 0
% 2.44/1.32  #Define  : 0
% 2.44/1.32  #Split   : 0
% 2.44/1.32  #Chain   : 0
% 2.44/1.32  #Close   : 0
% 2.44/1.32  
% 2.44/1.32  Ordering : KBO
% 2.44/1.32  
% 2.44/1.32  Simplification rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Subsume      : 4
% 2.44/1.32  #Demod        : 96
% 2.44/1.32  #Tautology    : 62
% 2.44/1.32  #SimpNegUnit  : 0
% 2.44/1.32  #BackRed      : 2
% 2.44/1.32  
% 2.44/1.32  #Partial instantiations: 0
% 2.44/1.32  #Strategies tried      : 1
% 2.44/1.32  
% 2.44/1.32  Timing (in seconds)
% 2.44/1.32  ----------------------
% 2.44/1.32  Preprocessing        : 0.27
% 2.44/1.32  Parsing              : 0.14
% 2.44/1.32  CNF conversion       : 0.01
% 2.44/1.32  Main loop            : 0.28
% 2.44/1.32  Inferencing          : 0.12
% 2.44/1.32  Reduction            : 0.10
% 2.44/1.32  Demodulation         : 0.09
% 2.44/1.32  BG Simplification    : 0.02
% 2.44/1.32  Subsumption          : 0.04
% 2.44/1.32  Abstraction          : 0.03
% 2.44/1.32  MUC search           : 0.00
% 2.44/1.32  Cooper               : 0.00
% 2.44/1.32  Total                : 0.58
% 2.44/1.32  Index Insertion      : 0.00
% 2.44/1.32  Index Deletion       : 0.00
% 2.44/1.32  Index Matching       : 0.00
% 2.44/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
