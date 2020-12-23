%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:50 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (  11 expanded)
%              Number of equality atoms :    8 (  10 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_13,C_14,B_15,D_16] : k2_enumset1(A_13,C_14,B_15,D_16) = k2_enumset1(A_13,B_15,C_14,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,C_7,B_6,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:10:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  
% 1.82/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.14  
% 1.82/1.14  %Foreground sorts:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Background operators:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Foreground operators:
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.14  
% 1.82/1.15  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 1.82/1.15  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 1.82/1.15  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 1.82/1.15  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.15  tff(c_37, plain, (![A_13, C_14, B_15, D_16]: (k2_enumset1(A_13, C_14, B_15, D_16)=k2_enumset1(A_13, B_15, C_14, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.15  tff(c_76, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, C_7, B_6, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.82/1.15  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.15  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.82/1.15  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_7])).
% 1.82/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  Inference rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Ref     : 0
% 1.82/1.15  #Sup     : 48
% 1.82/1.15  #Fact    : 0
% 1.82/1.15  #Define  : 0
% 1.82/1.15  #Split   : 0
% 1.82/1.15  #Chain   : 0
% 1.82/1.15  #Close   : 0
% 1.82/1.15  
% 1.82/1.15  Ordering : KBO
% 1.82/1.15  
% 1.82/1.15  Simplification rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Subsume      : 18
% 1.82/1.15  #Demod        : 2
% 1.82/1.15  #Tautology    : 20
% 1.82/1.15  #SimpNegUnit  : 0
% 1.82/1.15  #BackRed      : 1
% 1.82/1.15  
% 1.82/1.15  #Partial instantiations: 0
% 1.82/1.15  #Strategies tried      : 1
% 1.82/1.15  
% 1.82/1.15  Timing (in seconds)
% 1.82/1.15  ----------------------
% 1.82/1.15  Preprocessing        : 0.25
% 1.82/1.15  Parsing              : 0.13
% 1.82/1.15  CNF conversion       : 0.01
% 1.82/1.15  Main loop            : 0.15
% 1.82/1.15  Inferencing          : 0.06
% 1.82/1.15  Reduction            : 0.06
% 1.82/1.15  Demodulation         : 0.05
% 1.82/1.15  BG Simplification    : 0.01
% 1.82/1.15  Subsumption          : 0.02
% 1.82/1.15  Abstraction          : 0.01
% 1.82/1.15  MUC search           : 0.00
% 1.82/1.15  Cooper               : 0.00
% 1.82/1.15  Total                : 0.42
% 1.82/1.15  Index Insertion      : 0.00
% 1.82/1.15  Index Deletion       : 0.00
% 1.82/1.15  Index Matching       : 0.00
% 1.82/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
