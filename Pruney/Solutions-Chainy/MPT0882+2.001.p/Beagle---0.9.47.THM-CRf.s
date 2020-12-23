%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k2_tarski(C,D)) = k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(A,B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_mcart_1)).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k2_tarski(k4_tarski(A_38,B_39),k4_tarski(A_38,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_8,B_9,B_39,C_10] : k2_zfmisc_1(k1_tarski(k4_tarski(A_8,B_9)),k2_tarski(B_39,C_10)) = k2_tarski(k4_tarski(k4_tarski(A_8,B_9),B_39),k3_mcart_1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_196,plain,(
    ! [A_8,B_9,B_39,C_10] : k2_zfmisc_1(k1_tarski(k4_tarski(A_8,B_9)),k2_tarski(B_39,C_10)) = k2_tarski(k3_mcart_1(A_8,B_9,B_39),k3_mcart_1(A_8,B_9,C_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_189])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_zfmisc_1(k1_tarski(A_3),k1_tarski(B_4)) = k1_tarski(k4_tarski(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_21,B_22,C_23] : k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k3_zfmisc_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_3,B_4,C_23] : k3_zfmisc_1(k1_tarski(A_3),k1_tarski(B_4),C_23) = k2_zfmisc_1(k1_tarski(k4_tarski(A_3,B_4)),C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_14,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_1130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.52  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.52  
% 3.23/1.52  %Foreground sorts:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Background operators:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Foreground operators:
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.23/1.52  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.23/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.52  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.52  
% 3.23/1.52  tff(f_35, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.23/1.52  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.23/1.52  tff(f_29, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 3.23/1.52  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.23/1.52  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k2_tarski(C, D)) = k2_tarski(k3_mcart_1(A, B, C), k3_mcart_1(A, B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_mcart_1)).
% 3.23/1.52  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.52  tff(c_145, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k1_tarski(A_38), k2_tarski(B_39, C_40))=k2_tarski(k4_tarski(A_38, B_39), k4_tarski(A_38, C_40)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.52  tff(c_189, plain, (![A_8, B_9, B_39, C_10]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_8, B_9)), k2_tarski(B_39, C_10))=k2_tarski(k4_tarski(k4_tarski(A_8, B_9), B_39), k3_mcart_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 3.23/1.52  tff(c_196, plain, (![A_8, B_9, B_39, C_10]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_8, B_9)), k2_tarski(B_39, C_10))=k2_tarski(k3_mcart_1(A_8, B_9, B_39), k3_mcart_1(A_8, B_9, C_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_189])).
% 3.23/1.52  tff(c_4, plain, (![A_3, B_4]: (k2_zfmisc_1(k1_tarski(A_3), k1_tarski(B_4))=k1_tarski(k4_tarski(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.52  tff(c_48, plain, (![A_21, B_22, C_23]: (k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k3_zfmisc_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.52  tff(c_63, plain, (![A_3, B_4, C_23]: (k3_zfmisc_1(k1_tarski(A_3), k1_tarski(B_4), C_23)=k2_zfmisc_1(k1_tarski(k4_tarski(A_3, B_4)), C_23))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 3.23/1.52  tff(c_14, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.52  tff(c_143, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_14])).
% 3.23/1.52  tff(c_1130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_143])).
% 3.23/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  Inference rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Ref     : 0
% 3.23/1.52  #Sup     : 280
% 3.23/1.52  #Fact    : 0
% 3.23/1.52  #Define  : 0
% 3.23/1.52  #Split   : 0
% 3.23/1.52  #Chain   : 0
% 3.23/1.52  #Close   : 0
% 3.23/1.52  
% 3.23/1.52  Ordering : KBO
% 3.23/1.52  
% 3.23/1.52  Simplification rules
% 3.23/1.52  ----------------------
% 3.23/1.52  #Subsume      : 33
% 3.23/1.52  #Demod        : 125
% 3.23/1.52  #Tautology    : 95
% 3.23/1.52  #SimpNegUnit  : 0
% 3.23/1.52  #BackRed      : 1
% 3.23/1.52  
% 3.23/1.52  #Partial instantiations: 0
% 3.23/1.52  #Strategies tried      : 1
% 3.23/1.52  
% 3.23/1.52  Timing (in seconds)
% 3.23/1.52  ----------------------
% 3.23/1.53  Preprocessing        : 0.28
% 3.23/1.53  Parsing              : 0.15
% 3.23/1.53  CNF conversion       : 0.01
% 3.23/1.53  Main loop            : 0.48
% 3.23/1.53  Inferencing          : 0.19
% 3.23/1.53  Reduction            : 0.19
% 3.23/1.53  Demodulation         : 0.16
% 3.23/1.53  BG Simplification    : 0.03
% 3.23/1.53  Subsumption          : 0.05
% 3.23/1.53  Abstraction          : 0.04
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.78
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
