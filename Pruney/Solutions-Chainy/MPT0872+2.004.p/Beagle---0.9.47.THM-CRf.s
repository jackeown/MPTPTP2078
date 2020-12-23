%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  20 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_46,plain,(
    ! [A_31,B_32,C_33,D_34] : k4_tarski(k4_tarski(k4_tarski(A_31,B_32),C_33),D_34) = k4_mcart_1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k4_tarski(k4_tarski(k4_tarski(A_9,B_10),C_11),D_12) = k4_mcart_1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [C_52,D_49,B_50,D_53,A_51] : k4_mcart_1(k4_tarski(A_51,B_50),C_52,D_49,D_53) = k4_tarski(k4_mcart_1(A_51,B_50,C_52,D_49),D_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_21,plain,(
    ! [A_21,B_22,C_23,D_24] : k4_tarski(k3_mcart_1(A_21,B_22,C_23),D_24) = k4_mcart_1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_3,A_1,D_4,B_2] :
      ( C_3 = A_1
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_21,B_22,D_24,C_23,C_3,D_4] :
      ( k3_mcart_1(A_21,B_22,C_23) = C_3
      | k4_tarski(C_3,D_4) != k4_mcart_1(A_21,B_22,C_23,D_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_4])).

tff(c_103,plain,(
    ! [C_3,D_4,C_52,D_49,B_50,D_53,A_51] :
      ( k3_mcart_1(k4_tarski(A_51,B_50),C_52,D_49) = C_3
      | k4_tarski(k4_mcart_1(A_51,B_50,C_52,D_49),D_53) != k4_tarski(C_3,D_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_36])).

tff(c_180,plain,(
    ! [A_51,B_50,C_52,D_49] : k3_mcart_1(k4_tarski(A_51,B_50),C_52,D_49) = k4_mcart_1(A_51,B_50,C_52,D_49) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_103])).

tff(c_10,plain,(
    k3_mcart_1(k4_tarski('#skF_1','#skF_2'),'#skF_3','#skF_4') != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:31:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.23  
% 2.02/1.23  %Foreground sorts:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Background operators:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Foreground operators:
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.23  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.02/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.23  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.02/1.23  
% 2.05/1.23  tff(f_35, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.05/1.23  tff(f_33, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.05/1.23  tff(f_31, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 2.05/1.23  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_mcart_1)).
% 2.05/1.23  tff(c_46, plain, (![A_31, B_32, C_33, D_34]: (k4_tarski(k4_tarski(k4_tarski(A_31, B_32), C_33), D_34)=k4_mcart_1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.23  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k4_tarski(k4_tarski(k4_tarski(A_9, B_10), C_11), D_12)=k4_mcart_1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.23  tff(c_97, plain, (![C_52, D_49, B_50, D_53, A_51]: (k4_mcart_1(k4_tarski(A_51, B_50), C_52, D_49, D_53)=k4_tarski(k4_mcart_1(A_51, B_50, C_52, D_49), D_53))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 2.05/1.23  tff(c_21, plain, (![A_21, B_22, C_23, D_24]: (k4_tarski(k3_mcart_1(A_21, B_22, C_23), D_24)=k4_mcart_1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.23  tff(c_4, plain, (![C_3, A_1, D_4, B_2]: (C_3=A_1 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.23  tff(c_36, plain, (![A_21, B_22, D_24, C_23, C_3, D_4]: (k3_mcart_1(A_21, B_22, C_23)=C_3 | k4_tarski(C_3, D_4)!=k4_mcart_1(A_21, B_22, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_21, c_4])).
% 2.05/1.23  tff(c_103, plain, (![C_3, D_4, C_52, D_49, B_50, D_53, A_51]: (k3_mcart_1(k4_tarski(A_51, B_50), C_52, D_49)=C_3 | k4_tarski(k4_mcart_1(A_51, B_50, C_52, D_49), D_53)!=k4_tarski(C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_97, c_36])).
% 2.05/1.23  tff(c_180, plain, (![A_51, B_50, C_52, D_49]: (k3_mcart_1(k4_tarski(A_51, B_50), C_52, D_49)=k4_mcart_1(A_51, B_50, C_52, D_49))), inference(reflexivity, [status(thm), theory('equality')], [c_103])).
% 2.05/1.23  tff(c_10, plain, (k3_mcart_1(k4_tarski('#skF_1', '#skF_2'), '#skF_3', '#skF_4')!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.23  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_10])).
% 2.05/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  Inference rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Ref     : 4
% 2.05/1.23  #Sup     : 49
% 2.05/1.23  #Fact    : 0
% 2.05/1.23  #Define  : 0
% 2.05/1.23  #Split   : 0
% 2.05/1.23  #Chain   : 0
% 2.05/1.23  #Close   : 0
% 2.05/1.23  
% 2.05/1.23  Ordering : KBO
% 2.05/1.23  
% 2.05/1.23  Simplification rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Subsume      : 14
% 2.05/1.23  #Demod        : 12
% 2.05/1.23  #Tautology    : 13
% 2.05/1.23  #SimpNegUnit  : 0
% 2.05/1.23  #BackRed      : 2
% 2.05/1.23  
% 2.05/1.23  #Partial instantiations: 0
% 2.05/1.23  #Strategies tried      : 1
% 2.05/1.23  
% 2.05/1.23  Timing (in seconds)
% 2.05/1.23  ----------------------
% 2.05/1.24  Preprocessing        : 0.26
% 2.05/1.24  Parsing              : 0.15
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.18
% 2.05/1.24  Inferencing          : 0.08
% 2.05/1.24  Reduction            : 0.04
% 2.05/1.24  Demodulation         : 0.04
% 2.05/1.24  BG Simplification    : 0.01
% 2.05/1.24  Subsumption          : 0.04
% 2.05/1.24  Abstraction          : 0.01
% 2.05/1.24  MUC search           : 0.00
% 2.05/1.24  Cooper               : 0.00
% 2.05/1.24  Total                : 0.47
% 2.05/1.24  Index Insertion      : 0.00
% 2.05/1.24  Index Deletion       : 0.00
% 2.05/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
