%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(k3_xboole_0(A_14,C_15),k3_xboole_0(B_16,C_15))
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(k3_xboole_0(A_17,C_18),B_19)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(resolution,[status(thm)],[c_11,c_2])).

tff(c_8,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_8])).

tff(c_28,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.05  
% 1.46/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.05  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.57/1.05  
% 1.57/1.05  %Foreground sorts:
% 1.57/1.05  
% 1.57/1.05  
% 1.57/1.05  %Background operators:
% 1.57/1.05  
% 1.57/1.05  
% 1.57/1.05  %Foreground operators:
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.57/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.57/1.05  
% 1.57/1.06  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.57/1.06  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 1.57/1.06  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.57/1.06  tff(f_38, negated_conjecture, ~(![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.57/1.06  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.57/1.06  tff(c_11, plain, (![A_14, C_15, B_16]: (r1_tarski(k3_xboole_0(A_14, C_15), k3_xboole_0(B_16, C_15)) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.06  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.06  tff(c_16, plain, (![A_17, C_18, B_19]: (r1_tarski(k3_xboole_0(A_17, C_18), B_19) | ~r1_tarski(A_17, B_19))), inference(resolution, [status(thm)], [c_11, c_2])).
% 1.57/1.06  tff(c_8, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.57/1.06  tff(c_23, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_8])).
% 1.57/1.06  tff(c_28, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_23])).
% 1.57/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.06  
% 1.57/1.06  Inference rules
% 1.57/1.06  ----------------------
% 1.57/1.06  #Ref     : 0
% 1.57/1.06  #Sup     : 3
% 1.57/1.06  #Fact    : 0
% 1.57/1.06  #Define  : 0
% 1.57/1.06  #Split   : 0
% 1.57/1.06  #Chain   : 0
% 1.57/1.06  #Close   : 0
% 1.57/1.06  
% 1.57/1.06  Ordering : KBO
% 1.57/1.06  
% 1.57/1.06  Simplification rules
% 1.57/1.06  ----------------------
% 1.57/1.06  #Subsume      : 0
% 1.57/1.06  #Demod        : 1
% 1.57/1.06  #Tautology    : 0
% 1.57/1.06  #SimpNegUnit  : 0
% 1.57/1.06  #BackRed      : 0
% 1.57/1.06  
% 1.57/1.06  #Partial instantiations: 0
% 1.57/1.06  #Strategies tried      : 1
% 1.57/1.06  
% 1.57/1.06  Timing (in seconds)
% 1.57/1.06  ----------------------
% 1.57/1.07  Preprocessing        : 0.24
% 1.57/1.07  Parsing              : 0.13
% 1.57/1.07  CNF conversion       : 0.01
% 1.57/1.07  Main loop            : 0.07
% 1.57/1.07  Inferencing          : 0.03
% 1.57/1.07  Reduction            : 0.02
% 1.57/1.07  Demodulation         : 0.01
% 1.57/1.07  BG Simplification    : 0.01
% 1.57/1.07  Subsumption          : 0.01
% 1.57/1.07  Abstraction          : 0.00
% 1.57/1.07  MUC search           : 0.00
% 1.57/1.07  Cooper               : 0.00
% 1.57/1.07  Total                : 0.34
% 1.57/1.07  Index Insertion      : 0.00
% 1.57/1.07  Index Deletion       : 0.00
% 1.57/1.07  Index Matching       : 0.00
% 1.57/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
