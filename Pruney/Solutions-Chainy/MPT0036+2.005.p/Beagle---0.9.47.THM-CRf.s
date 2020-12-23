%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_6,B_7] : k2_xboole_0(k3_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_6,c_13])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,C_19)
      | ~ r1_tarski(k2_xboole_0(A_18,B_20),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_21,B_22,B_23] : r1_tarski(A_21,k2_xboole_0(k2_xboole_0(A_21,B_22),B_23)) ),
    inference(resolution,[status(thm)],[c_8,c_35])).

tff(c_54,plain,(
    ! [A_6,B_7,B_23] : r1_tarski(k3_xboole_0(A_6,B_7),k2_xboole_0(A_6,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.07  
% 1.54/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.08  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.54/1.08  
% 1.54/1.08  %Foreground sorts:
% 1.54/1.08  
% 1.54/1.08  
% 1.54/1.08  %Background operators:
% 1.54/1.08  
% 1.54/1.08  
% 1.54/1.08  %Foreground operators:
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.54/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.08  
% 1.54/1.09  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.54/1.09  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.54/1.09  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.54/1.09  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.54/1.09  tff(f_40, negated_conjecture, ~(![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.54/1.09  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.54/1.09  tff(c_13, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.54/1.09  tff(c_20, plain, (![A_6, B_7]: (k2_xboole_0(k3_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_6, c_13])).
% 1.54/1.09  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.54/1.09  tff(c_35, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, C_19) | ~r1_tarski(k2_xboole_0(A_18, B_20), C_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.09  tff(c_44, plain, (![A_21, B_22, B_23]: (r1_tarski(A_21, k2_xboole_0(k2_xboole_0(A_21, B_22), B_23)))), inference(resolution, [status(thm)], [c_8, c_35])).
% 1.54/1.09  tff(c_54, plain, (![A_6, B_7, B_23]: (r1_tarski(k3_xboole_0(A_6, B_7), k2_xboole_0(A_6, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_44])).
% 1.54/1.09  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.09  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 1.54/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.09  
% 1.54/1.09  Inference rules
% 1.54/1.09  ----------------------
% 1.54/1.09  #Ref     : 0
% 1.54/1.09  #Sup     : 10
% 1.54/1.09  #Fact    : 0
% 1.54/1.09  #Define  : 0
% 1.54/1.09  #Split   : 0
% 1.54/1.09  #Chain   : 0
% 1.54/1.09  #Close   : 0
% 1.54/1.09  
% 1.54/1.09  Ordering : KBO
% 1.54/1.09  
% 1.54/1.09  Simplification rules
% 1.54/1.09  ----------------------
% 1.54/1.09  #Subsume      : 0
% 1.54/1.09  #Demod        : 2
% 1.54/1.09  #Tautology    : 3
% 1.54/1.09  #SimpNegUnit  : 0
% 1.54/1.09  #BackRed      : 1
% 1.54/1.09  
% 1.54/1.09  #Partial instantiations: 0
% 1.54/1.09  #Strategies tried      : 1
% 1.54/1.09  
% 1.54/1.09  Timing (in seconds)
% 1.54/1.09  ----------------------
% 1.54/1.09  Preprocessing        : 0.25
% 1.54/1.09  Parsing              : 0.14
% 1.54/1.09  CNF conversion       : 0.01
% 1.54/1.09  Main loop            : 0.09
% 1.54/1.09  Inferencing          : 0.04
% 1.54/1.09  Reduction            : 0.02
% 1.54/1.09  Demodulation         : 0.02
% 1.54/1.09  BG Simplification    : 0.01
% 1.54/1.09  Subsumption          : 0.01
% 1.54/1.09  Abstraction          : 0.00
% 1.54/1.09  MUC search           : 0.00
% 1.54/1.09  Cooper               : 0.00
% 1.54/1.09  Total                : 0.36
% 1.54/1.09  Index Insertion      : 0.00
% 1.54/1.09  Index Deletion       : 0.00
% 1.54/1.09  Index Matching       : 0.00
% 1.54/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
