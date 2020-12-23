%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:30 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_58,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,k4_xboole_0(B_24,C_25))
      | ~ r1_xboole_0(A_23,C_25)
      | r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_23] :
      ( ~ r1_xboole_0(A_23,k1_xboole_0)
      | ~ r1_xboole_0(A_23,'#skF_2')
      | r1_xboole_0(A_23,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_58])).

tff(c_80,plain,(
    ! [A_26] :
      ( ~ r1_xboole_0(A_26,'#skF_2')
      | r1_xboole_0(A_26,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_92,plain,(
    ! [A_27] : r1_xboole_0(k4_xboole_0(A_27,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_27] : r1_xboole_0('#skF_1',k4_xboole_0(A_27,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.21  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.21  
% 1.78/1.21  %Foreground sorts:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Background operators:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Foreground operators:
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.21  
% 1.78/1.22  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.78/1.22  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.78/1.22  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.78/1.22  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.78/1.22  tff(f_45, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 1.78/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.78/1.22  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.22  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.22  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.78/1.22  tff(c_37, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.22  tff(c_45, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_37])).
% 1.78/1.22  tff(c_58, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, k4_xboole_0(B_24, C_25)) | ~r1_xboole_0(A_23, C_25) | r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.22  tff(c_61, plain, (![A_23]: (~r1_xboole_0(A_23, k1_xboole_0) | ~r1_xboole_0(A_23, '#skF_2') | r1_xboole_0(A_23, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_58])).
% 1.78/1.22  tff(c_80, plain, (![A_26]: (~r1_xboole_0(A_26, '#skF_2') | r1_xboole_0(A_26, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_61])).
% 1.78/1.22  tff(c_92, plain, (![A_27]: (r1_xboole_0(k4_xboole_0(A_27, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_80])).
% 1.78/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.22  tff(c_97, plain, (![A_27]: (r1_xboole_0('#skF_1', k4_xboole_0(A_27, '#skF_2')))), inference(resolution, [status(thm)], [c_92, c_2])).
% 1.78/1.22  tff(c_14, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.78/1.22  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_14])).
% 1.78/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  Inference rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Ref     : 0
% 1.78/1.22  #Sup     : 18
% 1.78/1.22  #Fact    : 0
% 1.78/1.22  #Define  : 0
% 1.78/1.22  #Split   : 0
% 1.78/1.22  #Chain   : 0
% 1.78/1.22  #Close   : 0
% 1.78/1.22  
% 1.78/1.22  Ordering : KBO
% 1.78/1.22  
% 1.78/1.22  Simplification rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Subsume      : 0
% 1.78/1.22  #Demod        : 10
% 1.78/1.22  #Tautology    : 10
% 1.78/1.22  #SimpNegUnit  : 0
% 1.78/1.22  #BackRed      : 1
% 1.78/1.22  
% 1.78/1.22  #Partial instantiations: 0
% 1.78/1.22  #Strategies tried      : 1
% 1.78/1.22  
% 1.78/1.22  Timing (in seconds)
% 1.78/1.22  ----------------------
% 1.78/1.22  Preprocessing        : 0.28
% 1.78/1.22  Parsing              : 0.16
% 1.78/1.22  CNF conversion       : 0.02
% 1.78/1.22  Main loop            : 0.12
% 1.78/1.23  Inferencing          : 0.05
% 1.78/1.23  Reduction            : 0.03
% 1.78/1.23  Demodulation         : 0.03
% 1.78/1.23  BG Simplification    : 0.01
% 1.78/1.23  Subsumption          : 0.02
% 1.78/1.23  Abstraction          : 0.00
% 1.78/1.23  MUC search           : 0.00
% 1.78/1.23  Cooper               : 0.00
% 1.78/1.23  Total                : 0.43
% 1.78/1.23  Index Insertion      : 0.00
% 1.78/1.23  Index Deletion       : 0.00
% 1.78/1.23  Index Matching       : 0.00
% 1.78/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
