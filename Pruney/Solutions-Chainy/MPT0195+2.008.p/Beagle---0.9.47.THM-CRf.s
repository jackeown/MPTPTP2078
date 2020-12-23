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
% DateTime   : Thu Dec  3 09:47:01 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (  13 expanded)
%              Number of equality atoms :    8 (  12 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_13,A_14,D_15,C_16] : k2_enumset1(B_13,A_14,D_15,C_16) = k2_enumset1(A_14,B_13,C_16,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(B_6,A_5,D_8,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.30  
% 2.02/1.30  %Foreground sorts:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Background operators:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Foreground operators:
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.30  
% 2.02/1.31  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 2.02/1.31  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_enumset1)).
% 2.02/1.31  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 2.02/1.31  tff(c_4, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.31  tff(c_37, plain, (![B_13, A_14, D_15, C_16]: (k2_enumset1(B_13, A_14, D_15, C_16)=k2_enumset1(A_14, B_13, C_16, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.31  tff(c_76, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(B_6, A_5, D_8, C_7))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 2.02/1.31  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.31  tff(c_7, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 2.02/1.31  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_7])).
% 2.02/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  Inference rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Ref     : 0
% 2.02/1.31  #Sup     : 80
% 2.02/1.31  #Fact    : 0
% 2.02/1.31  #Define  : 0
% 2.02/1.31  #Split   : 0
% 2.02/1.31  #Chain   : 0
% 2.02/1.31  #Close   : 0
% 2.02/1.31  
% 2.02/1.31  Ordering : KBO
% 2.02/1.31  
% 2.02/1.31  Simplification rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Subsume      : 22
% 2.02/1.31  #Demod        : 3
% 2.02/1.31  #Tautology    : 28
% 2.02/1.31  #SimpNegUnit  : 0
% 2.02/1.31  #BackRed      : 1
% 2.02/1.31  
% 2.02/1.31  #Partial instantiations: 0
% 2.02/1.31  #Strategies tried      : 1
% 2.02/1.31  
% 2.02/1.31  Timing (in seconds)
% 2.02/1.31  ----------------------
% 2.02/1.31  Preprocessing        : 0.30
% 2.02/1.31  Parsing              : 0.14
% 2.02/1.31  CNF conversion       : 0.02
% 2.02/1.31  Main loop            : 0.22
% 2.02/1.31  Inferencing          : 0.08
% 2.02/1.31  Reduction            : 0.09
% 2.02/1.31  Demodulation         : 0.08
% 2.02/1.31  BG Simplification    : 0.02
% 2.02/1.31  Subsumption          : 0.03
% 2.02/1.31  Abstraction          : 0.01
% 2.02/1.31  MUC search           : 0.00
% 2.02/1.31  Cooper               : 0.00
% 2.02/1.31  Total                : 0.54
% 2.02/1.31  Index Insertion      : 0.00
% 2.02/1.31  Index Deletion       : 0.00
% 2.02/1.31  Index Matching       : 0.00
% 2.02/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
