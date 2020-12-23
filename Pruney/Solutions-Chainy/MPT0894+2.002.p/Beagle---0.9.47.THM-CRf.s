%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  14 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_17,plain,(
    ! [A_1,B_2,C_3,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_10) = k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_35,plain,(
    ! [A_1,B_2,C_3,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_10) = k4_zfmisc_1(A_1,B_2,C_3,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7,c_17])).

tff(c_6,plain,(
    k3_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.59/1.12  
% 1.59/1.12  %Foreground sorts:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Background operators:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Foreground operators:
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.12  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 1.59/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.12  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.12  
% 1.59/1.13  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.59/1.13  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 1.59/1.13  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k2_zfmisc_1(A, B), C, D) = k4_zfmisc_1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_mcart_1)).
% 1.59/1.13  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.13  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_4, B_5), C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.13  tff(c_7, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.59/1.13  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.13  tff(c_17, plain, (![A_1, B_2, C_3, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_10)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_10))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8])).
% 1.59/1.13  tff(c_35, plain, (![A_1, B_2, C_3, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_10)=k4_zfmisc_1(A_1, B_2, C_3, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_7, c_17])).
% 1.59/1.13  tff(c_6, plain, (k3_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3', '#skF_4')!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.59/1.13  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_6])).
% 1.59/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  Inference rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Ref     : 0
% 1.59/1.13  #Sup     : 7
% 1.59/1.13  #Fact    : 0
% 1.59/1.13  #Define  : 0
% 1.59/1.13  #Split   : 0
% 1.59/1.13  #Chain   : 0
% 1.59/1.13  #Close   : 0
% 1.59/1.13  
% 1.59/1.13  Ordering : KBO
% 1.59/1.13  
% 1.59/1.13  Simplification rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Subsume      : 0
% 1.59/1.13  #Demod        : 3
% 1.59/1.13  #Tautology    : 4
% 1.59/1.13  #SimpNegUnit  : 0
% 1.59/1.13  #BackRed      : 1
% 1.59/1.13  
% 1.59/1.13  #Partial instantiations: 0
% 1.59/1.13  #Strategies tried      : 1
% 1.59/1.13  
% 1.59/1.13  Timing (in seconds)
% 1.59/1.13  ----------------------
% 1.59/1.13  Preprocessing        : 0.22
% 1.59/1.13  Parsing              : 0.12
% 1.59/1.13  CNF conversion       : 0.01
% 1.59/1.13  Main loop            : 0.07
% 1.59/1.13  Inferencing          : 0.04
% 1.59/1.13  Reduction            : 0.02
% 1.59/1.13  Demodulation         : 0.02
% 1.59/1.13  BG Simplification    : 0.01
% 1.59/1.13  Subsumption          : 0.01
% 1.59/1.13  Abstraction          : 0.00
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.32
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
