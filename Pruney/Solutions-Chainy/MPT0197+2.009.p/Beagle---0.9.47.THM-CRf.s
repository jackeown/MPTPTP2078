%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:04 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   20 (  29 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  21 expanded)
%              Number of equality atoms :   11 (  20 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_13,C_14,D_15,B_16] : k2_enumset1(A_13,C_14,D_15,B_16) = k2_enumset1(A_13,B_16,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [C_7,B_6,D_8,A_5] : k2_enumset1(C_7,B_6,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [C_14,B_16,D_15,A_13] : k2_enumset1(C_14,B_16,D_15,A_13) = k2_enumset1(A_13,C_14,D_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7])).

tff(c_172,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.16  
% 1.75/1.16  %Foreground sorts:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Background operators:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Foreground operators:
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.16  
% 1.75/1.16  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 1.75/1.16  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 1.75/1.16  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_enumset1)).
% 1.75/1.16  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.16  tff(c_38, plain, (![A_13, C_14, D_15, B_16]: (k2_enumset1(A_13, C_14, D_15, B_16)=k2_enumset1(A_13, B_16, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.16  tff(c_4, plain, (![C_7, B_6, D_8, A_5]: (k2_enumset1(C_7, B_6, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.16  tff(c_56, plain, (![C_14, B_16, D_15, A_13]: (k2_enumset1(C_14, B_16, D_15, A_13)=k2_enumset1(A_13, C_14, D_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4])).
% 1.75/1.16  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.16  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 1.75/1.16  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7])).
% 1.75/1.16  tff(c_172, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8])).
% 1.75/1.16  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_172])).
% 1.75/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  Inference rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Ref     : 0
% 1.75/1.16  #Sup     : 48
% 1.75/1.16  #Fact    : 0
% 1.75/1.16  #Define  : 0
% 1.75/1.16  #Split   : 0
% 1.75/1.16  #Chain   : 0
% 1.75/1.16  #Close   : 0
% 1.75/1.16  
% 1.75/1.16  Ordering : KBO
% 1.75/1.16  
% 1.75/1.16  Simplification rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Subsume      : 17
% 1.75/1.16  #Demod        : 6
% 1.75/1.16  #Tautology    : 16
% 1.75/1.16  #SimpNegUnit  : 0
% 1.75/1.16  #BackRed      : 1
% 1.75/1.16  
% 1.75/1.16  #Partial instantiations: 0
% 1.75/1.16  #Strategies tried      : 1
% 1.75/1.16  
% 1.75/1.16  Timing (in seconds)
% 1.75/1.16  ----------------------
% 1.75/1.17  Preprocessing        : 0.24
% 1.75/1.17  Parsing              : 0.12
% 1.75/1.17  CNF conversion       : 0.01
% 1.75/1.17  Main loop            : 0.16
% 1.75/1.17  Inferencing          : 0.06
% 1.75/1.17  Reduction            : 0.06
% 1.75/1.17  Demodulation         : 0.06
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.02
% 1.75/1.17  Abstraction          : 0.01
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.42
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
