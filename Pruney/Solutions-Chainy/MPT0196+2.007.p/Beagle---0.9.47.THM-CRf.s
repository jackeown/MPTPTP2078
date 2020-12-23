%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:02 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   25 (  41 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  32 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_103,plain,(
    ! [A_25,C_26,D_27,B_28] : k2_enumset1(A_25,C_26,D_27,B_28) = k2_enumset1(A_25,B_28,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_25,B_28,D_27,C_26] : k2_enumset1(A_25,B_28,D_27,C_26) = k2_enumset1(A_25,B_28,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_6])).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1,D_4] : k2_enumset1(C_3,B_2,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [C_26,B_28,A_25,D_27] : k2_enumset1(C_26,B_28,A_25,D_27) = k2_enumset1(A_25,C_26,D_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_3','#skF_1','#skF_4','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_423,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_12])).

tff(c_424,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_423])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  
% 2.91/1.42  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.91/1.42  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.91/1.42  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 2.91/1.42  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 2.91/1.42  tff(c_103, plain, (![A_25, C_26, D_27, B_28]: (k2_enumset1(A_25, C_26, D_27, B_28)=k2_enumset1(A_25, B_28, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.42  tff(c_6, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.42  tff(c_139, plain, (![A_25, B_28, D_27, C_26]: (k2_enumset1(A_25, B_28, D_27, C_26)=k2_enumset1(A_25, B_28, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_103, c_6])).
% 2.91/1.42  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.42  tff(c_2, plain, (![C_3, B_2, A_1, D_4]: (k2_enumset1(C_3, B_2, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.42  tff(c_121, plain, (![C_26, B_28, A_25, D_27]: (k2_enumset1(C_26, B_28, A_25, D_27)=k2_enumset1(A_25, C_26, D_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 2.91/1.42  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.42  tff(c_11, plain, (k2_enumset1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_10])).
% 2.91/1.42  tff(c_12, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 2.91/1.42  tff(c_423, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_12])).
% 2.91/1.42  tff(c_424, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_423])).
% 2.91/1.42  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_424])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 290
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 0
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 96
% 2.91/1.42  #Demod        : 8
% 2.91/1.42  #Tautology    : 54
% 2.91/1.42  #SimpNegUnit  : 0
% 2.91/1.42  #BackRed      : 1
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.43  Preprocessing        : 0.26
% 2.91/1.43  Parsing              : 0.14
% 2.91/1.43  CNF conversion       : 0.01
% 2.91/1.43  Main loop            : 0.38
% 2.91/1.43  Inferencing          : 0.12
% 2.91/1.43  Reduction            : 0.17
% 2.91/1.43  Demodulation         : 0.16
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.06
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.66
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
