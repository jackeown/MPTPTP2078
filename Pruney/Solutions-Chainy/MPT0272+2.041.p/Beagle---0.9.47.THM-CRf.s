%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:11 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_14,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_27,plain,(
    ! [B_11,A_12] :
      ( k1_tarski(B_11) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [B_13,B_14] :
      ( k4_xboole_0(k1_tarski(B_13),B_14) = k1_tarski(B_13)
      | k4_xboole_0(k1_tarski(B_13),B_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_27])).

tff(c_12,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_12])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  
% 1.55/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.55/1.07  
% 1.55/1.07  %Foreground sorts:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Background operators:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Foreground operators:
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.55/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.55/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.07  
% 1.55/1.07  tff(f_40, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.55/1.07  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.55/1.07  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.55/1.07  tff(c_14, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.55/1.07  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.55/1.07  tff(c_27, plain, (![B_11, A_12]: (k1_tarski(B_11)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.55/1.07  tff(c_47, plain, (![B_13, B_14]: (k4_xboole_0(k1_tarski(B_13), B_14)=k1_tarski(B_13) | k4_xboole_0(k1_tarski(B_13), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_27])).
% 1.55/1.07  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.55/1.07  tff(c_53, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47, c_12])).
% 1.55/1.07  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_53])).
% 1.55/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  
% 1.55/1.07  Inference rules
% 1.55/1.07  ----------------------
% 1.55/1.07  #Ref     : 0
% 1.55/1.08  #Sup     : 10
% 1.55/1.08  #Fact    : 1
% 1.55/1.08  #Define  : 0
% 1.55/1.08  #Split   : 0
% 1.55/1.08  #Chain   : 0
% 1.55/1.08  #Close   : 0
% 1.55/1.08  
% 1.55/1.08  Ordering : KBO
% 1.55/1.08  
% 1.55/1.08  Simplification rules
% 1.55/1.08  ----------------------
% 1.55/1.08  #Subsume      : 0
% 1.55/1.08  #Demod        : 0
% 1.55/1.08  #Tautology    : 5
% 1.55/1.08  #SimpNegUnit  : 1
% 1.55/1.08  #BackRed      : 0
% 1.55/1.08  
% 1.55/1.08  #Partial instantiations: 0
% 1.55/1.08  #Strategies tried      : 1
% 1.55/1.08  
% 1.55/1.08  Timing (in seconds)
% 1.55/1.08  ----------------------
% 1.55/1.08  Preprocessing        : 0.25
% 1.55/1.08  Parsing              : 0.13
% 1.55/1.08  CNF conversion       : 0.01
% 1.55/1.08  Main loop            : 0.07
% 1.62/1.08  Inferencing          : 0.03
% 1.62/1.08  Reduction            : 0.02
% 1.62/1.08  Demodulation         : 0.01
% 1.62/1.08  BG Simplification    : 0.01
% 1.62/1.08  Subsumption          : 0.01
% 1.62/1.08  Abstraction          : 0.01
% 1.62/1.08  MUC search           : 0.00
% 1.62/1.08  Cooper               : 0.00
% 1.62/1.08  Total                : 0.34
% 1.62/1.08  Index Insertion      : 0.00
% 1.62/1.08  Index Deletion       : 0.00
% 1.62/1.08  Index Matching       : 0.00
% 1.62/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
