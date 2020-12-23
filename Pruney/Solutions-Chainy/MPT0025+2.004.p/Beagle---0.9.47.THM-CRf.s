%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:34 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k3_xboole_0(B,C))
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [C_20] :
      ( r1_tarski('#skF_1',C_20)
      | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_54,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.14  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.56/1.14  
% 1.56/1.14  %Foreground sorts:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Background operators:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Foreground operators:
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.14  
% 1.56/1.15  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.56/1.15  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.56/1.15  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.56/1.15  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.56/1.15  tff(c_8, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.15  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.15  tff(c_10, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.15  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.15  tff(c_20, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_12])).
% 1.56/1.15  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.15  tff(c_46, plain, (![C_20]: (r1_tarski('#skF_1', C_20) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), C_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2])).
% 1.56/1.15  tff(c_54, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_46])).
% 1.56/1.15  tff(c_59, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_54])).
% 1.56/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.15  
% 1.56/1.15  Inference rules
% 1.56/1.15  ----------------------
% 1.56/1.15  #Ref     : 0
% 1.56/1.15  #Sup     : 11
% 1.56/1.15  #Fact    : 0
% 1.56/1.15  #Define  : 0
% 1.56/1.15  #Split   : 0
% 1.56/1.15  #Chain   : 0
% 1.56/1.15  #Close   : 0
% 1.56/1.15  
% 1.56/1.15  Ordering : KBO
% 1.56/1.15  
% 1.56/1.15  Simplification rules
% 1.56/1.15  ----------------------
% 1.56/1.15  #Subsume      : 0
% 1.56/1.15  #Demod        : 0
% 1.56/1.15  #Tautology    : 4
% 1.56/1.15  #SimpNegUnit  : 1
% 1.56/1.15  #BackRed      : 0
% 1.56/1.15  
% 1.56/1.15  #Partial instantiations: 0
% 1.56/1.15  #Strategies tried      : 1
% 1.56/1.15  
% 1.56/1.15  Timing (in seconds)
% 1.56/1.15  ----------------------
% 1.56/1.15  Preprocessing        : 0.26
% 1.56/1.15  Parsing              : 0.14
% 1.56/1.15  CNF conversion       : 0.02
% 1.56/1.15  Main loop            : 0.09
% 1.56/1.15  Inferencing          : 0.04
% 1.56/1.15  Reduction            : 0.02
% 1.56/1.15  Demodulation         : 0.01
% 1.56/1.15  BG Simplification    : 0.01
% 1.56/1.15  Subsumption          : 0.01
% 1.56/1.15  Abstraction          : 0.00
% 1.56/1.15  MUC search           : 0.00
% 1.56/1.15  Cooper               : 0.00
% 1.56/1.15  Total                : 0.38
% 1.56/1.15  Index Insertion      : 0.00
% 1.56/1.15  Index Deletion       : 0.00
% 1.56/1.15  Index Matching       : 0.00
% 1.56/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
