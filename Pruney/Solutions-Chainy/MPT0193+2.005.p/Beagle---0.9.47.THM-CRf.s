%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:58 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   21 (  29 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (  17 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_35,C_36,A_37,D_38] : k2_enumset1(B_35,C_36,A_37,D_38) = k2_enumset1(A_37,B_35,C_36,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [B_6,C_7,D_8,A_5] : k2_enumset1(B_6,C_7,D_8,A_5) = k2_enumset1(B_6,C_7,A_5,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_14,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_4,c_14])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:59:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.21  
% 2.12/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.12/1.22  
% 2.12/1.22  %Foreground sorts:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Background operators:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Foreground operators:
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  
% 2.12/1.22  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 2.12/1.22  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 2.12/1.22  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 2.12/1.22  tff(c_4, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.22  tff(c_45, plain, (![B_35, C_36, A_37, D_38]: (k2_enumset1(B_35, C_36, A_37, D_38)=k2_enumset1(A_37, B_35, C_36, D_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.22  tff(c_87, plain, (![B_6, C_7, D_8, A_5]: (k2_enumset1(B_6, C_7, D_8, A_5)=k2_enumset1(B_6, C_7, A_5, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 2.12/1.22  tff(c_14, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.22  tff(c_15, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_4, c_14])).
% 2.12/1.22  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_15])).
% 2.12/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  Inference rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Ref     : 0
% 2.12/1.22  #Sup     : 82
% 2.12/1.22  #Fact    : 0
% 2.12/1.22  #Define  : 0
% 2.12/1.22  #Split   : 0
% 2.12/1.22  #Chain   : 0
% 2.12/1.22  #Close   : 0
% 2.12/1.22  
% 2.12/1.22  Ordering : KBO
% 2.12/1.22  
% 2.12/1.22  Simplification rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Subsume      : 17
% 2.12/1.22  #Demod        : 5
% 2.12/1.22  #Tautology    : 22
% 2.12/1.22  #SimpNegUnit  : 0
% 2.12/1.22  #BackRed      : 1
% 2.12/1.22  
% 2.12/1.22  #Partial instantiations: 0
% 2.12/1.22  #Strategies tried      : 1
% 2.12/1.22  
% 2.12/1.22  Timing (in seconds)
% 2.12/1.22  ----------------------
% 2.12/1.23  Preprocessing        : 0.27
% 2.12/1.23  Parsing              : 0.14
% 2.12/1.23  CNF conversion       : 0.02
% 2.12/1.23  Main loop            : 0.20
% 2.12/1.23  Inferencing          : 0.07
% 2.12/1.23  Reduction            : 0.08
% 2.12/1.23  Demodulation         : 0.07
% 2.12/1.23  BG Simplification    : 0.02
% 2.12/1.23  Subsumption          : 0.03
% 2.12/1.23  Abstraction          : 0.01
% 2.12/1.23  MUC search           : 0.00
% 2.12/1.23  Cooper               : 0.00
% 2.12/1.23  Total                : 0.49
% 2.12/1.23  Index Insertion      : 0.00
% 2.12/1.23  Index Deletion       : 0.00
% 2.12/1.23  Index Matching       : 0.00
% 2.12/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
