%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:57 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   17 (  25 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :    9 (  17 expanded)
%              Number of equality atoms :    8 (  16 expanded)
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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(c_2,plain,(
    ! [A_1,D_4,C_3,B_2] : k2_enumset1(A_1,D_4,C_3,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_6,A_5,D_8,C_7] : k2_enumset1(B_6,A_5,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_1','#skF_2') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_4,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:13:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.02  
% 1.54/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.02  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.54/1.02  
% 1.54/1.02  %Foreground sorts:
% 1.54/1.02  
% 1.54/1.02  
% 1.54/1.02  %Background operators:
% 1.54/1.02  
% 1.54/1.02  
% 1.54/1.02  %Foreground operators:
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.54/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.02  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.02  tff('#skF_4', type, '#skF_4': $i).
% 1.54/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.03  
% 1.62/1.03  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 1.62/1.03  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_enumset1)).
% 1.62/1.03  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 1.62/1.03  tff(c_2, plain, (![A_1, D_4, C_3, B_2]: (k2_enumset1(A_1, D_4, C_3, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.03  tff(c_4, plain, (![B_6, A_5, D_8, C_7]: (k2_enumset1(B_6, A_5, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.03  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.03  tff(c_7, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.62/1.03  tff(c_8, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_1', '#skF_2')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7])).
% 1.62/1.03  tff(c_10, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_4, c_8])).
% 1.62/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.03  
% 1.62/1.03  Inference rules
% 1.62/1.03  ----------------------
% 1.62/1.03  #Ref     : 0
% 1.62/1.03  #Sup     : 0
% 1.62/1.03  #Fact    : 0
% 1.62/1.03  #Define  : 0
% 1.62/1.03  #Split   : 0
% 1.62/1.03  #Chain   : 0
% 1.62/1.03  #Close   : 0
% 1.62/1.03  
% 1.62/1.03  Ordering : KBO
% 1.62/1.03  
% 1.62/1.03  Simplification rules
% 1.62/1.03  ----------------------
% 1.62/1.03  #Subsume      : 2
% 1.62/1.03  #Demod        : 6
% 1.62/1.03  #Tautology    : 0
% 1.62/1.03  #SimpNegUnit  : 0
% 1.62/1.03  #BackRed      : 0
% 1.62/1.03  
% 1.62/1.03  #Partial instantiations: 0
% 1.62/1.03  #Strategies tried      : 1
% 1.62/1.03  
% 1.62/1.03  Timing (in seconds)
% 1.62/1.03  ----------------------
% 1.62/1.04  Preprocessing        : 0.26
% 1.62/1.04  Parsing              : 0.14
% 1.62/1.04  CNF conversion       : 0.02
% 1.62/1.04  Main loop            : 0.03
% 1.62/1.04  Inferencing          : 0.00
% 1.62/1.04  Reduction            : 0.02
% 1.62/1.04  Demodulation         : 0.02
% 1.62/1.04  BG Simplification    : 0.01
% 1.62/1.04  Subsumption          : 0.01
% 1.62/1.04  Abstraction          : 0.00
% 1.62/1.04  MUC search           : 0.00
% 1.62/1.04  Cooper               : 0.00
% 1.62/1.04  Total                : 0.31
% 1.62/1.04  Index Insertion      : 0.00
% 1.62/1.04  Index Deletion       : 0.00
% 1.62/1.04  Index Matching       : 0.00
% 1.62/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
