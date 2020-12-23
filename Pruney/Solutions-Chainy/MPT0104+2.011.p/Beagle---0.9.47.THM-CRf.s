%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_14,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_86,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(k2_xboole_0(A_18,C_19),B_20)
      | ~ r1_tarski(C_19,B_20)
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_274,plain,(
    ! [A_31,B_32,B_33] :
      ( r1_tarski(k5_xboole_0(A_31,B_32),B_33)
      | ~ r1_tarski(k4_xboole_0(B_32,A_31),B_33)
      | ~ r1_tarski(k4_xboole_0(A_31,B_32),B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_86])).

tff(c_10,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_277,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_10])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.23  
% 1.93/1.24  tff(f_44, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 1.93/1.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.93/1.24  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 1.93/1.24  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.93/1.24  tff(c_14, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.24  tff(c_12, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.24  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.24  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.24  tff(c_15, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.93/1.24  tff(c_86, plain, (![A_18, C_19, B_20]: (r1_tarski(k2_xboole_0(A_18, C_19), B_20) | ~r1_tarski(C_19, B_20) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.24  tff(c_274, plain, (![A_31, B_32, B_33]: (r1_tarski(k5_xboole_0(A_31, B_32), B_33) | ~r1_tarski(k4_xboole_0(B_32, A_31), B_33) | ~r1_tarski(k4_xboole_0(A_31, B_32), B_33))), inference(superposition, [status(thm), theory('equality')], [c_15, c_86])).
% 1.93/1.24  tff(c_10, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.24  tff(c_277, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_274, c_10])).
% 1.93/1.24  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_277])).
% 1.93/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  Inference rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Ref     : 0
% 1.93/1.24  #Sup     : 70
% 1.93/1.24  #Fact    : 0
% 1.93/1.24  #Define  : 0
% 1.93/1.24  #Split   : 0
% 1.93/1.24  #Chain   : 0
% 1.93/1.24  #Close   : 0
% 1.93/1.24  
% 1.93/1.24  Ordering : KBO
% 1.93/1.24  
% 1.93/1.24  Simplification rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Subsume      : 0
% 1.93/1.24  #Demod        : 28
% 1.93/1.24  #Tautology    : 24
% 1.93/1.24  #SimpNegUnit  : 0
% 1.93/1.24  #BackRed      : 0
% 1.93/1.24  
% 1.93/1.24  #Partial instantiations: 0
% 1.93/1.24  #Strategies tried      : 1
% 1.93/1.24  
% 1.93/1.24  Timing (in seconds)
% 1.93/1.24  ----------------------
% 1.93/1.24  Preprocessing        : 0.27
% 1.93/1.24  Parsing              : 0.14
% 1.93/1.24  CNF conversion       : 0.02
% 1.93/1.24  Main loop            : 0.20
% 1.93/1.24  Inferencing          : 0.08
% 1.93/1.24  Reduction            : 0.07
% 1.93/1.24  Demodulation         : 0.06
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.03
% 1.93/1.24  Abstraction          : 0.02
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.50
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.24  Index Matching       : 0.00
% 1.93/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
