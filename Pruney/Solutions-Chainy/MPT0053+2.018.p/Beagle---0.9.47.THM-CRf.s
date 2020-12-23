%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:53 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_10])).

tff(c_8,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.11  
% 1.56/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.11  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.56/1.11  
% 1.56/1.11  %Foreground sorts:
% 1.56/1.11  
% 1.56/1.11  
% 1.56/1.11  %Background operators:
% 1.56/1.11  
% 1.56/1.11  
% 1.56/1.11  %Foreground operators:
% 1.56/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.11  
% 1.56/1.12  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.56/1.12  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.56/1.12  tff(f_34, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.56/1.12  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.12  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.12  tff(c_14, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_10])).
% 1.56/1.12  tff(c_8, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.56/1.12  tff(c_17, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_8])).
% 1.56/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.12  
% 1.56/1.12  Inference rules
% 1.56/1.12  ----------------------
% 1.56/1.12  #Ref     : 0
% 1.56/1.12  #Sup     : 1
% 1.56/1.12  #Fact    : 0
% 1.56/1.12  #Define  : 0
% 1.56/1.12  #Split   : 0
% 1.56/1.12  #Chain   : 0
% 1.56/1.12  #Close   : 0
% 1.56/1.12  
% 1.56/1.12  Ordering : KBO
% 1.56/1.12  
% 1.56/1.12  Simplification rules
% 1.56/1.12  ----------------------
% 1.56/1.12  #Subsume      : 0
% 1.56/1.12  #Demod        : 1
% 1.56/1.12  #Tautology    : 0
% 1.56/1.12  #SimpNegUnit  : 0
% 1.56/1.12  #BackRed      : 1
% 1.56/1.12  
% 1.56/1.12  #Partial instantiations: 0
% 1.56/1.12  #Strategies tried      : 1
% 1.56/1.12  
% 1.56/1.12  Timing (in seconds)
% 1.56/1.12  ----------------------
% 1.56/1.12  Preprocessing        : 0.24
% 1.56/1.12  Parsing              : 0.14
% 1.56/1.12  CNF conversion       : 0.01
% 1.56/1.12  Main loop            : 0.07
% 1.56/1.12  Inferencing          : 0.03
% 1.56/1.12  Reduction            : 0.02
% 1.56/1.12  Demodulation         : 0.01
% 1.56/1.12  BG Simplification    : 0.01
% 1.56/1.12  Subsumption          : 0.01
% 1.56/1.12  Abstraction          : 0.00
% 1.56/1.12  MUC search           : 0.00
% 1.56/1.12  Cooper               : 0.00
% 1.56/1.12  Total                : 0.33
% 1.56/1.12  Index Insertion      : 0.00
% 1.56/1.12  Index Deletion       : 0.00
% 1.56/1.12  Index Matching       : 0.00
% 1.56/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
