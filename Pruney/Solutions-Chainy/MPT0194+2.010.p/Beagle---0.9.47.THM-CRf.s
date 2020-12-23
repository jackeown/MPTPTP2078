%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:00 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(c_4,plain,(
    ! [B_6,D_8,A_5,C_7] : k2_enumset1(B_6,D_8,A_5,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.03  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.47/1.03  
% 1.47/1.03  %Foreground sorts:
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  %Background operators:
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  %Foreground operators:
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.47/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.47/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.03  tff('#skF_4', type, '#skF_4': $i).
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.03  
% 1.47/1.04  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 1.47/1.04  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 1.47/1.04  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 1.47/1.04  tff(c_4, plain, (![B_6, D_8, A_5, C_7]: (k2_enumset1(B_6, D_8, A_5, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.47/1.04  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.47/1.04  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.47/1.04  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_6])).
% 1.47/1.04  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7])).
% 1.47/1.04  tff(c_10, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.47/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.04  
% 1.47/1.04  Inference rules
% 1.47/1.04  ----------------------
% 1.47/1.04  #Ref     : 0
% 1.47/1.04  #Sup     : 0
% 1.47/1.04  #Fact    : 0
% 1.47/1.04  #Define  : 0
% 1.47/1.04  #Split   : 0
% 1.47/1.04  #Chain   : 0
% 1.47/1.04  #Close   : 0
% 1.47/1.04  
% 1.47/1.04  Ordering : KBO
% 1.47/1.04  
% 1.47/1.04  Simplification rules
% 1.47/1.04  ----------------------
% 1.47/1.04  #Subsume      : 2
% 1.47/1.04  #Demod        : 6
% 1.47/1.04  #Tautology    : 0
% 1.47/1.04  #SimpNegUnit  : 0
% 1.47/1.04  #BackRed      : 0
% 1.47/1.04  
% 1.47/1.04  #Partial instantiations: 0
% 1.47/1.04  #Strategies tried      : 1
% 1.47/1.04  
% 1.47/1.04  Timing (in seconds)
% 1.47/1.04  ----------------------
% 1.47/1.05  Preprocessing        : 0.25
% 1.47/1.05  Parsing              : 0.13
% 1.47/1.05  CNF conversion       : 0.01
% 1.47/1.05  Main loop            : 0.03
% 1.47/1.05  Inferencing          : 0.00
% 1.47/1.05  Reduction            : 0.02
% 1.47/1.05  Demodulation         : 0.02
% 1.47/1.05  BG Simplification    : 0.01
% 1.47/1.05  Subsumption          : 0.01
% 1.47/1.05  Abstraction          : 0.00
% 1.47/1.05  MUC search           : 0.00
% 1.47/1.05  Cooper               : 0.00
% 1.47/1.05  Total                : 0.31
% 1.47/1.05  Index Insertion      : 0.00
% 1.47/1.05  Index Deletion       : 0.00
% 1.47/1.05  Index Matching       : 0.00
% 1.47/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
