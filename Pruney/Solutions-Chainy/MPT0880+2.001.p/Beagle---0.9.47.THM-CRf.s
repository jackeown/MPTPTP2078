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
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
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
    ~ ! [A,B,C,D] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k2_tarski(k4_tarski(A_3,C_5),k4_tarski(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_31,B_32,C_33] : k2_zfmisc_1(k2_tarski(A_31,B_32),k1_tarski(C_33)) = k2_tarski(k4_tarski(A_31,C_33),k4_tarski(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_3,B_4,C_5,C_33] : k2_zfmisc_1(k2_zfmisc_1(k2_tarski(A_3,B_4),k1_tarski(C_5)),k1_tarski(C_33)) = k2_tarski(k4_tarski(k4_tarski(A_3,C_5),C_33),k4_tarski(k4_tarski(B_4,C_5),C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_117])).

tff(c_165,plain,(
    ! [A_3,B_4,C_5,C_33] : k3_zfmisc_1(k2_tarski(A_3,B_4),k1_tarski(C_5),k1_tarski(C_33)) = k2_tarski(k3_mcart_1(A_3,C_5,C_33),k3_mcart_1(B_4,C_5,C_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_8,c_142])).

tff(c_12,plain,(
    k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:19:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.53  
% 3.13/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.53  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.33/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.53  
% 3.33/1.54  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.33/1.54  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.33/1.54  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.33/1.54  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_mcart_1)).
% 3.33/1.54  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.54  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.54  tff(c_6, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_tarski(A_3, B_4), k1_tarski(C_5))=k2_tarski(k4_tarski(A_3, C_5), k4_tarski(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.54  tff(c_117, plain, (![A_31, B_32, C_33]: (k2_zfmisc_1(k2_tarski(A_31, B_32), k1_tarski(C_33))=k2_tarski(k4_tarski(A_31, C_33), k4_tarski(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.54  tff(c_142, plain, (![A_3, B_4, C_5, C_33]: (k2_zfmisc_1(k2_zfmisc_1(k2_tarski(A_3, B_4), k1_tarski(C_5)), k1_tarski(C_33))=k2_tarski(k4_tarski(k4_tarski(A_3, C_5), C_33), k4_tarski(k4_tarski(B_4, C_5), C_33)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_117])).
% 3.33/1.54  tff(c_165, plain, (![A_3, B_4, C_5, C_33]: (k3_zfmisc_1(k2_tarski(A_3, B_4), k1_tarski(C_5), k1_tarski(C_33))=k2_tarski(k3_mcart_1(A_3, C_5, C_33), k3_mcart_1(B_4, C_5, C_33)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_8, c_142])).
% 3.33/1.54  tff(c_12, plain, (k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.33/1.54  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_12])).
% 3.33/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  Inference rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Ref     : 0
% 3.33/1.54  #Sup     : 281
% 3.33/1.54  #Fact    : 0
% 3.33/1.54  #Define  : 0
% 3.33/1.54  #Split   : 0
% 3.33/1.54  #Chain   : 0
% 3.33/1.54  #Close   : 0
% 3.33/1.54  
% 3.33/1.54  Ordering : KBO
% 3.33/1.54  
% 3.33/1.54  Simplification rules
% 3.33/1.54  ----------------------
% 3.33/1.54  #Subsume      : 32
% 3.33/1.54  #Demod        : 122
% 3.33/1.54  #Tautology    : 93
% 3.33/1.54  #SimpNegUnit  : 0
% 3.33/1.54  #BackRed      : 1
% 3.33/1.54  
% 3.33/1.54  #Partial instantiations: 0
% 3.33/1.54  #Strategies tried      : 1
% 3.33/1.54  
% 3.33/1.54  Timing (in seconds)
% 3.33/1.54  ----------------------
% 3.33/1.54  Preprocessing        : 0.27
% 3.33/1.54  Parsing              : 0.14
% 3.33/1.54  CNF conversion       : 0.01
% 3.33/1.54  Main loop            : 0.46
% 3.33/1.54  Inferencing          : 0.18
% 3.33/1.54  Reduction            : 0.18
% 3.33/1.54  Demodulation         : 0.15
% 3.33/1.54  BG Simplification    : 0.03
% 3.33/1.54  Subsumption          : 0.05
% 3.33/1.54  Abstraction          : 0.04
% 3.33/1.54  MUC search           : 0.00
% 3.33/1.54  Cooper               : 0.00
% 3.33/1.54  Total                : 0.76
% 3.33/1.54  Index Insertion      : 0.00
% 3.33/1.54  Index Deletion       : 0.00
% 3.33/1.54  Index Matching       : 0.00
% 3.33/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
