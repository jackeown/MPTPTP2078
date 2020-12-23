%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:06 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   18 (  26 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  18 expanded)
%              Number of equality atoms :    9 (  17 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(c_4,plain,(
    ! [B_6,D_8,C_7,A_5] : k2_enumset1(B_6,D_8,C_7,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_13,C_14,B_15,D_16] : k2_enumset1(A_13,C_14,B_15,D_16) = k2_enumset1(A_13,B_15,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [B_17,C_18,D_19,A_20] : k2_enumset1(B_17,C_18,D_19,A_20) = k2_enumset1(A_20,B_17,C_18,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_163,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_6])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.22  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.80/1.22  
% 1.80/1.22  %Foreground sorts:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Background operators:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Foreground operators:
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.22  
% 1.80/1.22  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 1.80/1.22  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 1.80/1.22  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 1.80/1.22  tff(c_4, plain, (![B_6, D_8, C_7, A_5]: (k2_enumset1(B_6, D_8, C_7, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.22  tff(c_37, plain, (![A_13, C_14, B_15, D_16]: (k2_enumset1(A_13, C_14, B_15, D_16)=k2_enumset1(A_13, B_15, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.22  tff(c_94, plain, (![B_17, C_18, D_19, A_20]: (k2_enumset1(B_17, C_18, D_19, A_20)=k2_enumset1(A_20, B_17, C_18, D_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.80/1.22  tff(c_163, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 1.80/1.22  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.22  tff(c_7, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_6])).
% 1.80/1.22  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_7])).
% 1.80/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  Inference rules
% 1.80/1.22  ----------------------
% 1.80/1.22  #Ref     : 0
% 1.80/1.22  #Sup     : 80
% 1.80/1.22  #Fact    : 0
% 1.80/1.22  #Define  : 0
% 1.80/1.22  #Split   : 0
% 1.80/1.22  #Chain   : 0
% 1.80/1.22  #Close   : 0
% 1.80/1.22  
% 1.80/1.22  Ordering : KBO
% 1.80/1.22  
% 1.80/1.22  Simplification rules
% 1.80/1.22  ----------------------
% 1.80/1.22  #Subsume      : 26
% 1.80/1.22  #Demod        : 4
% 1.80/1.22  #Tautology    : 20
% 1.80/1.22  #SimpNegUnit  : 0
% 1.80/1.22  #BackRed      : 1
% 1.80/1.22  
% 1.80/1.22  #Partial instantiations: 0
% 1.80/1.22  #Strategies tried      : 1
% 1.80/1.22  
% 1.80/1.22  Timing (in seconds)
% 1.80/1.22  ----------------------
% 1.80/1.23  Preprocessing        : 0.24
% 1.80/1.23  Parsing              : 0.12
% 1.80/1.23  CNF conversion       : 0.01
% 1.80/1.23  Main loop            : 0.20
% 1.80/1.23  Inferencing          : 0.07
% 1.80/1.23  Reduction            : 0.08
% 1.80/1.23  Demodulation         : 0.07
% 1.80/1.23  BG Simplification    : 0.01
% 1.80/1.23  Subsumption          : 0.03
% 1.80/1.23  Abstraction          : 0.01
% 1.80/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.46
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
