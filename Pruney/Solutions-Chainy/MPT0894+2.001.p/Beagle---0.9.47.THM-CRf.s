%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   3 average)

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7,c_2])).

tff(c_34,plain,(
    ! [A_8,B_9,C_10,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_3) = k4_zfmisc_1(A_8,B_9,C_10,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_6,plain,(
    k3_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.09  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.09  
% 1.65/1.09  %Foreground sorts:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Background operators:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Foreground operators:
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.09  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 1.65/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.09  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.09  
% 1.65/1.09  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 1.65/1.09  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.65/1.09  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k2_zfmisc_1(A, B), C, D) = k4_zfmisc_1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_mcart_1)).
% 1.65/1.09  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.09  tff(c_7, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.09  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.09  tff(c_10, plain, (![A_8, B_9, C_10, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), C_3))), inference(superposition, [status(thm), theory('equality')], [c_7, c_2])).
% 1.65/1.09  tff(c_34, plain, (![A_8, B_9, C_10, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_3)=k4_zfmisc_1(A_8, B_9, C_10, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.65/1.09  tff(c_6, plain, (k3_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3', '#skF_4')!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.09  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 1.65/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  Inference rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Ref     : 0
% 1.65/1.09  #Sup     : 7
% 1.65/1.09  #Fact    : 0
% 1.65/1.09  #Define  : 0
% 1.65/1.09  #Split   : 0
% 1.65/1.09  #Chain   : 0
% 1.65/1.09  #Close   : 0
% 1.65/1.09  
% 1.65/1.09  Ordering : KBO
% 1.65/1.09  
% 1.65/1.09  Simplification rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Subsume      : 0
% 1.65/1.09  #Demod        : 2
% 1.65/1.09  #Tautology    : 4
% 1.65/1.10  #SimpNegUnit  : 0
% 1.65/1.10  #BackRed      : 1
% 1.65/1.10  
% 1.65/1.10  #Partial instantiations: 0
% 1.65/1.10  #Strategies tried      : 1
% 1.65/1.10  
% 1.65/1.10  Timing (in seconds)
% 1.65/1.10  ----------------------
% 1.65/1.10  Preprocessing        : 0.25
% 1.65/1.10  Parsing              : 0.14
% 1.65/1.10  CNF conversion       : 0.01
% 1.65/1.10  Main loop            : 0.08
% 1.65/1.10  Inferencing          : 0.04
% 1.65/1.10  Reduction            : 0.02
% 1.65/1.10  Demodulation         : 0.02
% 1.65/1.10  BG Simplification    : 0.01
% 1.65/1.10  Subsumption          : 0.01
% 1.65/1.10  Abstraction          : 0.00
% 1.65/1.10  MUC search           : 0.00
% 1.65/1.10  Cooper               : 0.00
% 1.65/1.10  Total                : 0.35
% 1.65/1.10  Index Insertion      : 0.00
% 1.65/1.10  Index Deletion       : 0.00
% 1.65/1.10  Index Matching       : 0.00
% 1.65/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
