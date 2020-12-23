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
% DateTime   : Thu Dec  3 09:47:04 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.60s
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

tff(c_2,plain,(
    ! [C_3,B_2,A_1,D_4] : k2_enumset1(C_3,B_2,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_13,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  
% 1.50/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.50/1.06  
% 1.50/1.06  %Foreground sorts:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Background operators:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Foreground operators:
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.50/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.50/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.50/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.06  tff('#skF_4', type, '#skF_4': $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.06  
% 1.60/1.07  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 1.60/1.07  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 1.60/1.07  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 1.60/1.07  tff(c_2, plain, (![C_3, B_2, A_1, D_4]: (k2_enumset1(C_3, B_2, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.07  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.07  tff(c_10, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.07  tff(c_11, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.60/1.07  tff(c_13, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 1.60/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  Inference rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Ref     : 0
% 1.60/1.07  #Sup     : 0
% 1.60/1.07  #Fact    : 0
% 1.60/1.07  #Define  : 0
% 1.60/1.07  #Split   : 0
% 1.60/1.07  #Chain   : 0
% 1.60/1.07  #Close   : 0
% 1.60/1.07  
% 1.60/1.07  Ordering : KBO
% 1.60/1.07  
% 1.60/1.07  Simplification rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Subsume      : 4
% 1.60/1.07  #Demod        : 2
% 1.60/1.07  #Tautology    : 0
% 1.60/1.07  #SimpNegUnit  : 0
% 1.60/1.07  #BackRed      : 0
% 1.60/1.07  
% 1.60/1.07  #Partial instantiations: 0
% 1.60/1.07  #Strategies tried      : 1
% 1.60/1.07  
% 1.60/1.07  Timing (in seconds)
% 1.60/1.07  ----------------------
% 1.60/1.07  Preprocessing        : 0.27
% 1.60/1.07  Parsing              : 0.14
% 1.60/1.07  CNF conversion       : 0.01
% 1.60/1.07  Main loop            : 0.03
% 1.60/1.07  Inferencing          : 0.00
% 1.60/1.07  Reduction            : 0.02
% 1.60/1.07  Demodulation         : 0.02
% 1.60/1.07  BG Simplification    : 0.01
% 1.60/1.07  Subsumption          : 0.01
% 1.60/1.07  Abstraction          : 0.00
% 1.60/1.07  MUC search           : 0.00
% 1.60/1.07  Cooper               : 0.00
% 1.60/1.07  Total                : 0.33
% 1.60/1.07  Index Insertion      : 0.00
% 1.60/1.07  Index Deletion       : 0.00
% 1.60/1.07  Index Matching       : 0.00
% 1.60/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
