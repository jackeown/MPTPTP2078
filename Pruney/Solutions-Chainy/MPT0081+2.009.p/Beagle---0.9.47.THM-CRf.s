%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  31 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),A_28) = A_28 ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [B_29] : k3_xboole_0(k1_xboole_0,B_29) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_12])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_350,plain,(
    ! [A_42,B_43,C_44] : k3_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k3_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_389,plain,(
    ! [C_44] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_44)) = k3_xboole_0(k1_xboole_0,C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_350])).

tff(c_405,plain,(
    ! [C_44] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_44)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_389])).

tff(c_55,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_24])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.60  
% 2.38/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.60  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.38/1.60  
% 2.38/1.60  %Foreground sorts:
% 2.38/1.60  
% 2.38/1.60  
% 2.38/1.60  %Background operators:
% 2.38/1.60  
% 2.38/1.60  
% 2.38/1.60  %Foreground operators:
% 2.38/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.60  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.60  
% 2.38/1.62  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.38/1.62  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.38/1.62  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.38/1.62  tff(f_54, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.38/1.62  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.38/1.62  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.38/1.62  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.62  tff(c_60, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.62  tff(c_88, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), A_28)=A_28)), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.38/1.62  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.62  tff(c_95, plain, (![B_29]: (k3_xboole_0(k1_xboole_0, B_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_88, c_12])).
% 2.38/1.62  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.62  tff(c_133, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.62  tff(c_141, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.38/1.62  tff(c_350, plain, (![A_42, B_43, C_44]: (k3_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k3_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.62  tff(c_389, plain, (![C_44]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_44))=k3_xboole_0(k1_xboole_0, C_44))), inference(superposition, [status(thm), theory('equality')], [c_141, c_350])).
% 2.38/1.62  tff(c_405, plain, (![C_44]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_44))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_389])).
% 2.38/1.62  tff(c_55, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.62  tff(c_24, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.62  tff(c_59, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_24])).
% 2.38/1.62  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_59])).
% 2.38/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.62  
% 2.38/1.62  Inference rules
% 2.38/1.62  ----------------------
% 2.38/1.62  #Ref     : 0
% 2.38/1.62  #Sup     : 92
% 2.38/1.62  #Fact    : 0
% 2.38/1.62  #Define  : 0
% 2.38/1.62  #Split   : 0
% 2.38/1.62  #Chain   : 0
% 2.38/1.62  #Close   : 0
% 2.38/1.62  
% 2.38/1.62  Ordering : KBO
% 2.38/1.62  
% 2.38/1.62  Simplification rules
% 2.38/1.62  ----------------------
% 2.38/1.62  #Subsume      : 0
% 2.38/1.62  #Demod        : 41
% 2.38/1.62  #Tautology    : 70
% 2.38/1.62  #SimpNegUnit  : 0
% 2.38/1.62  #BackRed      : 1
% 2.38/1.62  
% 2.38/1.62  #Partial instantiations: 0
% 2.38/1.62  #Strategies tried      : 1
% 2.38/1.62  
% 2.38/1.62  Timing (in seconds)
% 2.38/1.62  ----------------------
% 2.38/1.63  Preprocessing        : 0.45
% 2.38/1.63  Parsing              : 0.25
% 2.38/1.63  CNF conversion       : 0.03
% 2.38/1.63  Main loop            : 0.33
% 2.38/1.63  Inferencing          : 0.14
% 2.38/1.63  Reduction            : 0.11
% 2.38/1.63  Demodulation         : 0.09
% 2.38/1.63  BG Simplification    : 0.02
% 2.38/1.63  Subsumption          : 0.04
% 2.38/1.63  Abstraction          : 0.01
% 2.38/1.63  MUC search           : 0.00
% 2.38/1.63  Cooper               : 0.00
% 2.38/1.63  Total                : 0.83
% 2.38/1.63  Index Insertion      : 0.00
% 2.38/1.63  Index Deletion       : 0.00
% 2.38/1.63  Index Matching       : 0.00
% 2.38/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
