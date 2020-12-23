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
% DateTime   : Thu Dec  3 09:44:46 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(B_8,A_7)) = k5_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),k5_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4])).

tff(c_6,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.03  
% 1.48/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.04  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.48/1.04  
% 1.48/1.04  %Foreground sorts:
% 1.48/1.04  
% 1.48/1.04  
% 1.48/1.04  %Background operators:
% 1.48/1.04  
% 1.48/1.04  
% 1.48/1.04  %Foreground operators:
% 1.48/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.48/1.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.48/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.48/1.04  
% 1.48/1.05  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.48/1.05  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.48/1.05  tff(f_32, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.48/1.05  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k4_xboole_0(B_8, A_7))=k5_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.05  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.05  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), k5_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4])).
% 1.48/1.05  tff(c_6, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.48/1.05  tff(c_22, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_6])).
% 1.48/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.05  
% 1.48/1.05  Inference rules
% 1.48/1.05  ----------------------
% 1.48/1.05  #Ref     : 0
% 1.48/1.05  #Sup     : 3
% 1.48/1.05  #Fact    : 0
% 1.48/1.05  #Define  : 0
% 1.48/1.05  #Split   : 0
% 1.48/1.05  #Chain   : 0
% 1.48/1.05  #Close   : 0
% 1.48/1.05  
% 1.48/1.05  Ordering : KBO
% 1.48/1.05  
% 1.48/1.05  Simplification rules
% 1.48/1.05  ----------------------
% 1.48/1.05  #Subsume      : 0
% 1.48/1.05  #Demod        : 1
% 1.48/1.05  #Tautology    : 2
% 1.48/1.05  #SimpNegUnit  : 0
% 1.48/1.05  #BackRed      : 1
% 1.48/1.05  
% 1.48/1.05  #Partial instantiations: 0
% 1.48/1.05  #Strategies tried      : 1
% 1.48/1.05  
% 1.48/1.05  Timing (in seconds)
% 1.48/1.05  ----------------------
% 1.48/1.05  Preprocessing        : 0.24
% 1.48/1.05  Parsing              : 0.13
% 1.48/1.05  CNF conversion       : 0.01
% 1.48/1.05  Main loop            : 0.06
% 1.48/1.05  Inferencing          : 0.03
% 1.48/1.05  Reduction            : 0.02
% 1.48/1.05  Demodulation         : 0.02
% 1.48/1.05  BG Simplification    : 0.01
% 1.48/1.05  Subsumption          : 0.00
% 1.48/1.05  Abstraction          : 0.00
% 1.48/1.05  MUC search           : 0.00
% 1.48/1.05  Cooper               : 0.00
% 1.48/1.05  Total                : 0.33
% 1.48/1.05  Index Insertion      : 0.00
% 1.48/1.05  Index Deletion       : 0.00
% 1.48/1.06  Index Matching       : 0.00
% 1.48/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
