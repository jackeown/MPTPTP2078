%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:07 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_2,plain,(
    ! [A_1,D_4,C_3,B_2] : k2_enumset1(A_1,D_4,C_3,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,D_8,C_7,A_5] : k2_enumset1(B_6,D_8,C_7,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_13,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.03  
% 1.52/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.03  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.52/1.03  
% 1.52/1.03  %Foreground sorts:
% 1.52/1.03  
% 1.52/1.03  
% 1.52/1.03  %Background operators:
% 1.52/1.03  
% 1.52/1.03  
% 1.52/1.03  %Foreground operators:
% 1.52/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.52/1.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.52/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.52/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.52/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.03  tff('#skF_4', type, '#skF_4': $i).
% 1.52/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.03  
% 1.52/1.04  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 1.52/1.04  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 1.52/1.04  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 1.52/1.04  tff(c_2, plain, (![A_1, D_4, C_3, B_2]: (k2_enumset1(A_1, D_4, C_3, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.52/1.04  tff(c_4, plain, (![B_6, D_8, C_7, A_5]: (k2_enumset1(B_6, D_8, C_7, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.04  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.04  tff(c_11, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.52/1.04  tff(c_13, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 1.52/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.04  
% 1.52/1.04  Inference rules
% 1.52/1.04  ----------------------
% 1.52/1.04  #Ref     : 0
% 1.52/1.04  #Sup     : 0
% 1.52/1.04  #Fact    : 0
% 1.52/1.04  #Define  : 0
% 1.52/1.04  #Split   : 0
% 1.52/1.04  #Chain   : 0
% 1.52/1.04  #Close   : 0
% 1.52/1.04  
% 1.52/1.04  Ordering : KBO
% 1.52/1.04  
% 1.52/1.04  Simplification rules
% 1.52/1.04  ----------------------
% 1.52/1.04  #Subsume      : 4
% 1.52/1.04  #Demod        : 2
% 1.52/1.04  #Tautology    : 0
% 1.52/1.04  #SimpNegUnit  : 0
% 1.52/1.04  #BackRed      : 0
% 1.52/1.04  
% 1.52/1.04  #Partial instantiations: 0
% 1.52/1.04  #Strategies tried      : 1
% 1.52/1.04  
% 1.52/1.04  Timing (in seconds)
% 1.52/1.04  ----------------------
% 1.52/1.04  Preprocessing        : 0.26
% 1.52/1.04  Parsing              : 0.14
% 1.52/1.04  CNF conversion       : 0.01
% 1.52/1.04  Main loop            : 0.03
% 1.52/1.04  Inferencing          : 0.00
% 1.52/1.04  Reduction            : 0.02
% 1.52/1.04  Demodulation         : 0.02
% 1.52/1.04  BG Simplification    : 0.01
% 1.52/1.04  Subsumption          : 0.01
% 1.52/1.04  Abstraction          : 0.00
% 1.52/1.04  MUC search           : 0.00
% 1.52/1.04  Cooper               : 0.00
% 1.52/1.04  Total                : 0.31
% 1.52/1.04  Index Insertion      : 0.00
% 1.52/1.04  Index Deletion       : 0.00
% 1.52/1.04  Index Matching       : 0.00
% 1.52/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
