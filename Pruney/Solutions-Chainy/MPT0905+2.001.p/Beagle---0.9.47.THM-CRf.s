%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:53 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  26 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C),k1_tarski(D)) = k1_tarski(k4_mcart_1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

tff(c_10,plain,(
    ! [A_10,B_11,C_12,D_13] : k4_tarski(k3_mcart_1(A_10,B_11,C_12),D_13) = k4_mcart_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k4_tarski(k4_tarski(A_4,B_5),C_6) = k3_mcart_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_zfmisc_1(k1_tarski(A_2),k1_tarski(B_3)) = k1_tarski(k4_tarski(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_24,B_25,C_26] : k2_zfmisc_1(k2_zfmisc_1(A_24,B_25),C_26) = k3_zfmisc_1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_2,B_3,C_26] : k3_zfmisc_1(k1_tarski(A_2),k1_tarski(B_3),C_26) = k2_zfmisc_1(k1_tarski(k4_tarski(A_2,B_3)),C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_43,B_44,C_45] : k3_zfmisc_1(k1_tarski(A_43),k1_tarski(B_44),C_45) = k2_zfmisc_1(k1_tarski(k4_tarski(A_43,B_44)),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_zfmisc_1(k3_zfmisc_1(A_14,B_15,C_16),D_17) = k4_zfmisc_1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_43,B_44,C_45,D_17] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_43,B_44)),C_45),D_17) = k4_zfmisc_1(k1_tarski(A_43),k1_tarski(B_44),C_45,D_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_12])).

tff(c_142,plain,(
    ! [A_43,B_44,C_45,D_17] : k4_zfmisc_1(k1_tarski(A_43),k1_tarski(B_44),C_45,D_17) = k3_zfmisc_1(k1_tarski(k4_tarski(A_43,B_44)),C_45,D_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_14,plain,(
    k4_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_198,plain,(
    k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_14])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6,c_4,c_63,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  %$ k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.19  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.88/1.19  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 1.88/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_35, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 1.88/1.20  tff(f_31, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.88/1.20  tff(f_29, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.88/1.20  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.88/1.20  tff(f_37, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 1.88/1.20  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k4_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C), k1_tarski(D)) = k1_tarski(k4_mcart_1(A, B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_mcart_1)).
% 1.88/1.20  tff(c_10, plain, (![A_10, B_11, C_12, D_13]: (k4_tarski(k3_mcart_1(A_10, B_11, C_12), D_13)=k4_mcart_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.20  tff(c_6, plain, (![A_4, B_5, C_6]: (k4_tarski(k4_tarski(A_4, B_5), C_6)=k3_mcart_1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.20  tff(c_4, plain, (![A_2, B_3]: (k2_zfmisc_1(k1_tarski(A_2), k1_tarski(B_3))=k1_tarski(k4_tarski(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.20  tff(c_48, plain, (![A_24, B_25, C_26]: (k2_zfmisc_1(k2_zfmisc_1(A_24, B_25), C_26)=k3_zfmisc_1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.20  tff(c_63, plain, (![A_2, B_3, C_26]: (k3_zfmisc_1(k1_tarski(A_2), k1_tarski(B_3), C_26)=k2_zfmisc_1(k1_tarski(k4_tarski(A_2, B_3)), C_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 1.88/1.20  tff(c_8, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.20  tff(c_131, plain, (![A_43, B_44, C_45]: (k3_zfmisc_1(k1_tarski(A_43), k1_tarski(B_44), C_45)=k2_zfmisc_1(k1_tarski(k4_tarski(A_43, B_44)), C_45))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 1.88/1.20  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_zfmisc_1(k3_zfmisc_1(A_14, B_15, C_16), D_17)=k4_zfmisc_1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.20  tff(c_137, plain, (![A_43, B_44, C_45, D_17]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(A_43, B_44)), C_45), D_17)=k4_zfmisc_1(k1_tarski(A_43), k1_tarski(B_44), C_45, D_17))), inference(superposition, [status(thm), theory('equality')], [c_131, c_12])).
% 1.88/1.20  tff(c_142, plain, (![A_43, B_44, C_45, D_17]: (k4_zfmisc_1(k1_tarski(A_43), k1_tarski(B_44), C_45, D_17)=k3_zfmisc_1(k1_tarski(k4_tarski(A_43, B_44)), C_45, D_17))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 1.88/1.20  tff(c_14, plain, (k4_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.20  tff(c_198, plain, (k3_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_14])).
% 1.88/1.20  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6, c_4, c_63, c_198])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 46
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 0
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 0
% 1.88/1.20  #Demod        : 19
% 1.88/1.20  #Tautology    : 24
% 1.88/1.20  #SimpNegUnit  : 0
% 1.88/1.20  #BackRed      : 1
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.20  Preprocessing        : 0.26
% 1.88/1.20  Parsing              : 0.13
% 1.88/1.20  CNF conversion       : 0.01
% 1.88/1.20  Main loop            : 0.15
% 1.88/1.20  Inferencing          : 0.07
% 1.88/1.20  Reduction            : 0.05
% 1.88/1.20  Demodulation         : 0.04
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.20  Subsumption          : 0.02
% 1.88/1.20  Abstraction          : 0.02
% 1.88/1.20  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.43
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.88/1.20  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
