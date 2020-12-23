%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_6])).

tff(c_17,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_14])).

tff(c_21,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.04  
% 1.47/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.05  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.56/1.05  
% 1.56/1.05  %Foreground sorts:
% 1.56/1.05  
% 1.56/1.05  
% 1.56/1.05  %Background operators:
% 1.56/1.05  
% 1.56/1.05  
% 1.56/1.05  %Foreground operators:
% 1.56/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.05  
% 1.56/1.06  tff(f_38, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.56/1.06  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.56/1.06  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.56/1.06  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.06  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.06  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.06  tff(c_6, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.06  tff(c_14, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_6])).
% 1.56/1.06  tff(c_17, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_14])).
% 1.56/1.06  tff(c_21, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_17])).
% 1.56/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.06  
% 1.56/1.06  Inference rules
% 1.56/1.06  ----------------------
% 1.56/1.06  #Ref     : 0
% 1.56/1.06  #Sup     : 2
% 1.56/1.06  #Fact    : 0
% 1.56/1.06  #Define  : 0
% 1.56/1.06  #Split   : 0
% 1.56/1.06  #Chain   : 0
% 1.56/1.06  #Close   : 0
% 1.56/1.06  
% 1.56/1.06  Ordering : KBO
% 1.56/1.06  
% 1.56/1.06  Simplification rules
% 1.56/1.06  ----------------------
% 1.56/1.06  #Subsume      : 0
% 1.56/1.06  #Demod        : 1
% 1.56/1.06  #Tautology    : 0
% 1.56/1.06  #SimpNegUnit  : 0
% 1.56/1.06  #BackRed      : 0
% 1.56/1.06  
% 1.56/1.06  #Partial instantiations: 0
% 1.56/1.06  #Strategies tried      : 1
% 1.56/1.06  
% 1.56/1.06  Timing (in seconds)
% 1.56/1.06  ----------------------
% 1.56/1.06  Preprocessing        : 0.24
% 1.56/1.06  Parsing              : 0.14
% 1.56/1.06  CNF conversion       : 0.01
% 1.56/1.06  Main loop            : 0.06
% 1.56/1.06  Inferencing          : 0.03
% 1.56/1.06  Reduction            : 0.01
% 1.56/1.06  Demodulation         : 0.01
% 1.56/1.06  BG Simplification    : 0.01
% 1.56/1.06  Subsumption          : 0.01
% 1.56/1.06  Abstraction          : 0.00
% 1.56/1.06  MUC search           : 0.00
% 1.56/1.06  Cooper               : 0.00
% 1.56/1.06  Total                : 0.33
% 1.56/1.06  Index Insertion      : 0.00
% 1.56/1.06  Index Deletion       : 0.00
% 1.56/1.06  Index Matching       : 0.00
% 1.56/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
