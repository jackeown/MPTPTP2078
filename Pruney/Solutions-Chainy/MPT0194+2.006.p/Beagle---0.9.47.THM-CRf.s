%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:59 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   21 (  27 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (  15 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_4,plain,(
    ! [B_6,D_8,A_5,C_7] : k2_enumset1(B_6,D_8,A_5,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [B_25,C_26,A_27,D_28] : k2_enumset1(B_25,C_26,A_27,D_28) = k2_enumset1(A_27,B_25,C_26,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [D_8,A_5,B_6,C_7] : k2_enumset1(D_8,A_5,B_6,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_10,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_10])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  %$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.66/1.12  
% 1.66/1.12  %Foreground sorts:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Background operators:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Foreground operators:
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.66/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.12  
% 1.79/1.13  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 1.79/1.13  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 1.79/1.13  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 1.79/1.13  tff(c_4, plain, (![B_6, D_8, A_5, C_7]: (k2_enumset1(B_6, D_8, A_5, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.13  tff(c_41, plain, (![B_25, C_26, A_27, D_28]: (k2_enumset1(B_25, C_26, A_27, D_28)=k2_enumset1(A_27, B_25, C_26, D_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.13  tff(c_89, plain, (![D_8, A_5, B_6, C_7]: (k2_enumset1(D_8, A_5, B_6, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 1.79/1.13  tff(c_10, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.13  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_10])).
% 1.79/1.13  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_11])).
% 1.79/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.13  
% 1.79/1.13  Inference rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Ref     : 0
% 1.79/1.13  #Sup     : 24
% 1.79/1.13  #Fact    : 0
% 1.79/1.13  #Define  : 0
% 1.79/1.13  #Split   : 0
% 1.79/1.13  #Chain   : 0
% 1.79/1.13  #Close   : 0
% 1.79/1.13  
% 1.79/1.13  Ordering : KBO
% 1.79/1.13  
% 1.79/1.13  Simplification rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Subsume      : 4
% 1.79/1.13  #Demod        : 4
% 1.79/1.13  #Tautology    : 8
% 1.79/1.13  #SimpNegUnit  : 0
% 1.79/1.13  #BackRed      : 1
% 1.79/1.13  
% 1.79/1.13  #Partial instantiations: 0
% 1.79/1.13  #Strategies tried      : 1
% 1.79/1.13  
% 1.79/1.13  Timing (in seconds)
% 1.79/1.13  ----------------------
% 1.79/1.13  Preprocessing        : 0.26
% 1.79/1.13  Parsing              : 0.14
% 1.79/1.13  CNF conversion       : 0.01
% 1.79/1.13  Main loop            : 0.10
% 1.79/1.13  Inferencing          : 0.04
% 1.79/1.13  Reduction            : 0.04
% 1.79/1.13  Demodulation         : 0.04
% 1.79/1.13  BG Simplification    : 0.01
% 1.79/1.13  Subsumption          : 0.01
% 1.79/1.13  Abstraction          : 0.01
% 1.79/1.13  MUC search           : 0.00
% 1.79/1.13  Cooper               : 0.00
% 1.79/1.13  Total                : 0.38
% 1.79/1.13  Index Insertion      : 0.00
% 1.79/1.13  Index Deletion       : 0.00
% 1.79/1.13  Index Matching       : 0.00
% 1.79/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
