%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(c_33,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),B_6) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [A_11,B_12] : k2_tarski(A_11,B_12) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_6])).

tff(c_8,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k1_xboole_0 = A_1
      | k2_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  %$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.59/1.11  
% 1.59/1.11  %Foreground sorts:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Background operators:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Foreground operators:
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.11  
% 1.59/1.12  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.59/1.12  tff(f_34, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.59/1.12  tff(f_38, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.59/1.12  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.59/1.12  tff(c_33, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.12  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.12  tff(c_41, plain, (![A_11, B_12]: (k2_tarski(A_11, B_12)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_33, c_6])).
% 1.59/1.12  tff(c_8, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.12  tff(c_2, plain, (![A_1, B_2]: (k1_xboole_0=A_1 | k2_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.12  tff(c_17, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8, c_2])).
% 1.59/1.12  tff(c_48, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_17])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 12
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 0
% 1.59/1.12  #Demod        : 1
% 1.59/1.12  #Tautology    : 9
% 1.59/1.12  #SimpNegUnit  : 1
% 1.59/1.12  #BackRed      : 2
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.59/1.12  Preprocessing        : 0.26
% 1.59/1.12  Parsing              : 0.14
% 1.59/1.12  CNF conversion       : 0.02
% 1.59/1.12  Main loop            : 0.06
% 1.59/1.12  Inferencing          : 0.03
% 1.59/1.12  Reduction            : 0.02
% 1.59/1.12  Demodulation         : 0.01
% 1.59/1.12  BG Simplification    : 0.01
% 1.59/1.12  Subsumption          : 0.01
% 1.59/1.12  Abstraction          : 0.00
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.35
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
