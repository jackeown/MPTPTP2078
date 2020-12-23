%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :    9 (  13 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(c_4,plain,(
    ! [A_5,C_7,B_6,D_8] : k2_enumset1(A_5,C_7,B_6,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.08  
% 1.49/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.08  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.49/1.08  
% 1.49/1.08  %Foreground sorts:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Background operators:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Foreground operators:
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.49/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.08  
% 1.49/1.09  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 1.49/1.09  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 1.49/1.09  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 1.49/1.09  tff(c_4, plain, (![A_5, C_7, B_6, D_8]: (k2_enumset1(A_5, C_7, B_6, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.09  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.49/1.09  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.09  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 1.49/1.09  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.49/1.09  tff(c_10, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.49/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.09  
% 1.49/1.09  Inference rules
% 1.49/1.09  ----------------------
% 1.49/1.09  #Ref     : 0
% 1.49/1.09  #Sup     : 0
% 1.49/1.09  #Fact    : 0
% 1.49/1.09  #Define  : 0
% 1.49/1.09  #Split   : 0
% 1.49/1.09  #Chain   : 0
% 1.49/1.09  #Close   : 0
% 1.49/1.09  
% 1.49/1.09  Ordering : KBO
% 1.49/1.09  
% 1.49/1.09  Simplification rules
% 1.49/1.09  ----------------------
% 1.49/1.09  #Subsume      : 2
% 1.49/1.09  #Demod        : 4
% 1.49/1.09  #Tautology    : 0
% 1.49/1.09  #SimpNegUnit  : 0
% 1.49/1.09  #BackRed      : 0
% 1.49/1.09  
% 1.49/1.09  #Partial instantiations: 0
% 1.49/1.09  #Strategies tried      : 1
% 1.49/1.09  
% 1.49/1.09  Timing (in seconds)
% 1.49/1.09  ----------------------
% 1.49/1.09  Preprocessing        : 0.26
% 1.49/1.09  Parsing              : 0.14
% 1.61/1.09  CNF conversion       : 0.01
% 1.61/1.09  Main loop            : 0.03
% 1.61/1.09  Inferencing          : 0.00
% 1.61/1.09  Reduction            : 0.02
% 1.61/1.09  Demodulation         : 0.02
% 1.61/1.09  BG Simplification    : 0.01
% 1.61/1.09  Subsumption          : 0.01
% 1.61/1.09  Abstraction          : 0.00
% 1.61/1.09  MUC search           : 0.00
% 1.61/1.09  Cooper               : 0.00
% 1.61/1.09  Total                : 0.31
% 1.61/1.09  Index Insertion      : 0.00
% 1.61/1.09  Index Deletion       : 0.00
% 1.61/1.09  Index Matching       : 0.00
% 1.61/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
