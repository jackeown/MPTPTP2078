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
% DateTime   : Thu Dec  3 09:47:08 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (  11 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_4,plain,(
    ! [C_7,B_6,D_8,A_5] : k2_enumset1(C_7,B_6,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [C_13,B_14,A_15,D_16] : k2_enumset1(C_13,B_14,A_15,D_16) = k2_enumset1(A_15,B_14,C_13,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [C_7,B_6,D_8,A_5] : k2_enumset1(C_7,B_6,D_8,A_5) = k2_enumset1(C_7,B_6,A_5,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  
% 1.68/1.12  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 1.68/1.12  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_enumset1)).
% 1.68/1.12  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 1.68/1.12  tff(c_4, plain, (![C_7, B_6, D_8, A_5]: (k2_enumset1(C_7, B_6, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.12  tff(c_37, plain, (![C_13, B_14, A_15, D_16]: (k2_enumset1(C_13, B_14, A_15, D_16)=k2_enumset1(A_15, B_14, C_13, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.12  tff(c_76, plain, (![C_7, B_6, D_8, A_5]: (k2_enumset1(C_7, B_6, D_8, A_5)=k2_enumset1(C_7, B_6, A_5, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.68/1.12  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.12  tff(c_7, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.68/1.12  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_7])).
% 1.68/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  Inference rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Ref     : 0
% 1.68/1.12  #Sup     : 48
% 1.68/1.12  #Fact    : 0
% 1.68/1.12  #Define  : 0
% 1.68/1.12  #Split   : 0
% 1.68/1.12  #Chain   : 0
% 1.68/1.12  #Close   : 0
% 1.68/1.12  
% 1.68/1.12  Ordering : KBO
% 1.68/1.12  
% 1.68/1.12  Simplification rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Subsume      : 18
% 1.68/1.12  #Demod        : 2
% 1.68/1.12  #Tautology    : 20
% 1.68/1.12  #SimpNegUnit  : 0
% 1.68/1.12  #BackRed      : 1
% 1.68/1.12  
% 1.68/1.12  #Partial instantiations: 0
% 1.68/1.12  #Strategies tried      : 1
% 1.68/1.12  
% 1.68/1.12  Timing (in seconds)
% 1.68/1.12  ----------------------
% 1.68/1.13  Preprocessing        : 0.24
% 1.68/1.13  Parsing              : 0.12
% 1.68/1.13  CNF conversion       : 0.01
% 1.68/1.13  Main loop            : 0.15
% 1.68/1.13  Inferencing          : 0.06
% 1.68/1.13  Reduction            : 0.06
% 1.68/1.13  Demodulation         : 0.05
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.02
% 1.68/1.13  Abstraction          : 0.01
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.41
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
