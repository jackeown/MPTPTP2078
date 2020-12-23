%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:05 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  27 expanded)
%              Number of equality atoms :   14 (  26 expanded)
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(c_47,plain,(
    ! [A_26,C_27,D_28,B_29] : k2_enumset1(A_26,C_27,D_28,B_29) = k2_enumset1(A_26,B_29,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_26,B_29,D_28,C_27] : k2_enumset1(A_26,B_29,D_28,C_27) = k2_enumset1(A_26,B_29,C_27,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_6])).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [C_30,B_31,A_32,D_33] : k2_enumset1(C_30,B_31,A_32,D_33) = k2_enumset1(A_32,B_31,C_30,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [C_30,A_32,D_33,B_31] : k2_enumset1(C_30,A_32,D_33,B_31) = k2_enumset1(A_32,B_31,C_30,D_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_4])).

tff(c_12,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_424,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_124,c_13])).

tff(c_425,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_424])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  
% 2.61/1.35  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.61/1.35  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.61/1.35  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 2.61/1.35  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 2.61/1.35  tff(c_47, plain, (![A_26, C_27, D_28, B_29]: (k2_enumset1(A_26, C_27, D_28, B_29)=k2_enumset1(A_26, B_29, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.35  tff(c_6, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.35  tff(c_71, plain, (![A_26, B_29, D_28, C_27]: (k2_enumset1(A_26, B_29, D_28, C_27)=k2_enumset1(A_26, B_29, C_27, D_28))), inference(superposition, [status(thm), theory('equality')], [c_47, c_6])).
% 2.61/1.35  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.35  tff(c_100, plain, (![C_30, B_31, A_32, D_33]: (k2_enumset1(C_30, B_31, A_32, D_33)=k2_enumset1(A_32, B_31, C_30, D_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.35  tff(c_124, plain, (![C_30, A_32, D_33, B_31]: (k2_enumset1(C_30, A_32, D_33, B_31)=k2_enumset1(A_32, B_31, C_30, D_33))), inference(superposition, [status(thm), theory('equality')], [c_100, c_4])).
% 2.61/1.35  tff(c_12, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.35  tff(c_13, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.61/1.35  tff(c_424, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_124, c_13])).
% 2.61/1.35  tff(c_425, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_424])).
% 2.61/1.35  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_425])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 226
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 0
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 70
% 2.61/1.35  #Demod        : 6
% 2.61/1.35  #Tautology    : 50
% 2.61/1.35  #SimpNegUnit  : 0
% 2.61/1.35  #BackRed      : 1
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.36  Preprocessing        : 0.26
% 2.61/1.36  Parsing              : 0.14
% 2.61/1.36  CNF conversion       : 0.01
% 2.61/1.36  Main loop            : 0.34
% 2.61/1.36  Inferencing          : 0.11
% 2.61/1.36  Reduction            : 0.15
% 2.61/1.36  Demodulation         : 0.14
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.05
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
