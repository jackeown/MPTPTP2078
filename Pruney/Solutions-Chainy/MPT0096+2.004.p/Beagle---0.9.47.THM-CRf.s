%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_xboole_0(k4_xboole_0(A_3,B_4),B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4])).

tff(c_6,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.12  
% 1.51/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.12  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.51/1.12  
% 1.51/1.12  %Foreground sorts:
% 1.51/1.12  
% 1.51/1.12  
% 1.51/1.12  %Background operators:
% 1.51/1.12  
% 1.51/1.12  
% 1.51/1.12  %Foreground operators:
% 1.51/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.51/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.51/1.12  
% 1.51/1.13  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.51/1.13  tff(f_29, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.51/1.13  tff(f_32, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 1.51/1.13  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_xboole_0(k4_xboole_0(A_3, B_4), B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.13  tff(c_17, plain, (![A_7, B_8]: (r1_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4])).
% 1.51/1.13  tff(c_6, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.51/1.13  tff(c_28, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17, c_6])).
% 1.51/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.13  
% 1.51/1.13  Inference rules
% 1.51/1.13  ----------------------
% 1.51/1.13  #Ref     : 0
% 1.51/1.13  #Sup     : 5
% 1.51/1.13  #Fact    : 0
% 1.51/1.13  #Define  : 0
% 1.51/1.13  #Split   : 0
% 1.51/1.13  #Chain   : 0
% 1.51/1.13  #Close   : 0
% 1.51/1.13  
% 1.51/1.13  Ordering : KBO
% 1.51/1.13  
% 1.51/1.13  Simplification rules
% 1.51/1.13  ----------------------
% 1.51/1.13  #Subsume      : 0
% 1.51/1.13  #Demod        : 1
% 1.51/1.13  #Tautology    : 2
% 1.51/1.13  #SimpNegUnit  : 0
% 1.51/1.13  #BackRed      : 1
% 1.51/1.13  
% 1.51/1.13  #Partial instantiations: 0
% 1.51/1.13  #Strategies tried      : 1
% 1.51/1.13  
% 1.51/1.13  Timing (in seconds)
% 1.51/1.13  ----------------------
% 1.51/1.13  Preprocessing        : 0.24
% 1.51/1.13  Parsing              : 0.13
% 1.51/1.13  CNF conversion       : 0.01
% 1.51/1.13  Main loop            : 0.07
% 1.51/1.13  Inferencing          : 0.04
% 1.51/1.13  Reduction            : 0.02
% 1.51/1.13  Demodulation         : 0.01
% 1.51/1.13  BG Simplification    : 0.01
% 1.51/1.13  Subsumption          : 0.01
% 1.51/1.13  Abstraction          : 0.00
% 1.51/1.13  MUC search           : 0.00
% 1.51/1.13  Cooper               : 0.00
% 1.51/1.13  Total                : 0.32
% 1.51/1.13  Index Insertion      : 0.00
% 1.51/1.13  Index Deletion       : 0.00
% 1.51/1.13  Index Matching       : 0.00
% 1.51/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
