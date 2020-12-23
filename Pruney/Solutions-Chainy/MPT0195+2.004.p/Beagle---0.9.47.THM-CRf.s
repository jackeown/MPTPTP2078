%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:01 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(c_41,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(A_15,B_13,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,A_5,C_7,D_8] : k2_enumset1(B_6,A_5,C_7,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_13,C_14,A_15,D_16] : k2_enumset1(B_13,C_14,A_15,D_16) = k2_enumset1(B_13,A_15,C_14,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.09  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.09  
% 1.67/1.09  %Foreground sorts:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Background operators:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Foreground operators:
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.09  
% 1.67/1.10  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l123_enumset1)).
% 1.67/1.10  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 1.67/1.10  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 1.67/1.10  tff(c_41, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(A_15, B_13, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_4, plain, (![B_6, A_5, C_7, D_8]: (k2_enumset1(B_6, A_5, C_7, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.10  tff(c_56, plain, (![B_13, C_14, A_15, D_16]: (k2_enumset1(B_13, C_14, A_15, D_16)=k2_enumset1(B_13, A_15, C_14, D_16))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 1.67/1.10  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.10  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.67/1.10  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_7])).
% 1.67/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  Inference rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Ref     : 0
% 1.67/1.10  #Sup     : 24
% 1.67/1.10  #Fact    : 0
% 1.67/1.10  #Define  : 0
% 1.67/1.10  #Split   : 0
% 1.67/1.10  #Chain   : 0
% 1.67/1.10  #Close   : 0
% 1.67/1.10  
% 1.67/1.10  Ordering : KBO
% 1.67/1.10  
% 1.67/1.10  Simplification rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Subsume      : 4
% 1.67/1.10  #Demod        : 2
% 1.67/1.10  #Tautology    : 12
% 1.67/1.10  #SimpNegUnit  : 0
% 1.67/1.10  #BackRed      : 1
% 1.67/1.10  
% 1.67/1.10  #Partial instantiations: 0
% 1.67/1.10  #Strategies tried      : 1
% 1.67/1.10  
% 1.67/1.10  Timing (in seconds)
% 1.67/1.10  ----------------------
% 1.67/1.10  Preprocessing        : 0.25
% 1.67/1.10  Parsing              : 0.13
% 1.67/1.10  CNF conversion       : 0.01
% 1.67/1.10  Main loop            : 0.11
% 1.67/1.10  Inferencing          : 0.04
% 1.67/1.10  Reduction            : 0.04
% 1.67/1.10  Demodulation         : 0.04
% 1.67/1.10  BG Simplification    : 0.01
% 1.67/1.10  Subsumption          : 0.01
% 1.67/1.10  Abstraction          : 0.01
% 1.67/1.10  MUC search           : 0.00
% 1.67/1.10  Cooper               : 0.00
% 1.67/1.10  Total                : 0.38
% 1.67/1.10  Index Insertion      : 0.00
% 1.67/1.10  Index Deletion       : 0.00
% 1.67/1.10  Index Matching       : 0.00
% 1.67/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
