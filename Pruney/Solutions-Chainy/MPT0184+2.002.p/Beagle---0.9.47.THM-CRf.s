%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:45 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   16 (  20 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :    9 (  13 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] : k1_enumset1(A_4,C_6,B_5) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k1_enumset1('#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k1_enumset1('#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_8,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.01  
% 1.47/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.01  %$ k1_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.47/1.01  
% 1.47/1.01  %Foreground sorts:
% 1.47/1.01  
% 1.47/1.01  
% 1.47/1.01  %Background operators:
% 1.47/1.01  
% 1.47/1.01  
% 1.47/1.01  %Foreground operators:
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.47/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.01  tff('#skF_3', type, '#skF_3': $i).
% 1.47/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.01  
% 1.47/1.02  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 1.47/1.02  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 1.47/1.02  tff(f_32, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 1.47/1.02  tff(c_4, plain, (![A_4, C_6, B_5]: (k1_enumset1(A_4, C_6, B_5)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.47/1.02  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.47/1.02  tff(c_6, plain, (k1_enumset1('#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.47/1.02  tff(c_7, plain, (k1_enumset1('#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 1.47/1.02  tff(c_8, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.47/1.02  tff(c_10, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.47/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.02  
% 1.47/1.02  Inference rules
% 1.47/1.02  ----------------------
% 1.47/1.02  #Ref     : 0
% 1.47/1.02  #Sup     : 0
% 1.47/1.02  #Fact    : 0
% 1.47/1.02  #Define  : 0
% 1.47/1.02  #Split   : 0
% 1.47/1.02  #Chain   : 0
% 1.47/1.02  #Close   : 0
% 1.47/1.02  
% 1.47/1.02  Ordering : KBO
% 1.47/1.02  
% 1.47/1.02  Simplification rules
% 1.47/1.02  ----------------------
% 1.47/1.02  #Subsume      : 2
% 1.47/1.02  #Demod        : 4
% 1.47/1.02  #Tautology    : 0
% 1.47/1.02  #SimpNegUnit  : 0
% 1.47/1.02  #BackRed      : 0
% 1.47/1.02  
% 1.47/1.02  #Partial instantiations: 0
% 1.47/1.02  #Strategies tried      : 1
% 1.47/1.02  
% 1.47/1.02  Timing (in seconds)
% 1.47/1.02  ----------------------
% 1.47/1.02  Preprocessing        : 0.24
% 1.47/1.02  Parsing              : 0.13
% 1.47/1.02  CNF conversion       : 0.01
% 1.47/1.02  Main loop            : 0.03
% 1.47/1.02  Inferencing          : 0.00
% 1.47/1.02  Reduction            : 0.02
% 1.47/1.02  Demodulation         : 0.02
% 1.47/1.02  BG Simplification    : 0.01
% 1.47/1.02  Subsumption          : 0.01
% 1.47/1.02  Abstraction          : 0.00
% 1.47/1.02  MUC search           : 0.00
% 1.47/1.02  Cooper               : 0.00
% 1.47/1.02  Total                : 0.29
% 1.47/1.02  Index Insertion      : 0.00
% 1.47/1.02  Index Deletion       : 0.00
% 1.47/1.02  Index Matching       : 0.00
% 1.47/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
