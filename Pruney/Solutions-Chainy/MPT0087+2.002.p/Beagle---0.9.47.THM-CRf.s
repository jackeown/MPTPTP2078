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
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  31 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [B_36] : k4_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_10])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_158])).

tff(c_565,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k3_xboole_0(A_52,B_53),C_54) = k3_xboole_0(A_52,k4_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_620,plain,(
    ! [C_54] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_54)) = k4_xboole_0(k1_xboole_0,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_565])).

tff(c_636,plain,(
    ! [C_54] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_54)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_620])).

tff(c_141,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_24])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.11/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.27  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.27  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.11/1.27  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.11/1.27  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.11/1.27  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.27  tff(c_149, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.27  tff(c_200, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), A_35)=A_35)), inference(resolution, [status(thm)], [c_14, c_149])).
% 2.11/1.27  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.27  tff(c_213, plain, (![B_36]: (k4_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_200, c_10])).
% 2.11/1.27  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.27  tff(c_158, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.27  tff(c_166, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_158])).
% 2.11/1.27  tff(c_565, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k3_xboole_0(A_52, B_53), C_54)=k3_xboole_0(A_52, k4_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.27  tff(c_620, plain, (![C_54]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_54))=k4_xboole_0(k1_xboole_0, C_54))), inference(superposition, [status(thm), theory('equality')], [c_166, c_565])).
% 2.11/1.27  tff(c_636, plain, (![C_54]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_54))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_620])).
% 2.11/1.27  tff(c_141, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.27  tff(c_24, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.27  tff(c_145, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_24])).
% 2.11/1.27  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_636, c_145])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 146
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 0
% 2.11/1.27  #Demod        : 70
% 2.11/1.27  #Tautology    : 111
% 2.11/1.27  #SimpNegUnit  : 0
% 2.11/1.27  #BackRed      : 1
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.27  Preprocessing        : 0.29
% 2.11/1.27  Parsing              : 0.16
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.23
% 2.11/1.27  Inferencing          : 0.09
% 2.11/1.27  Reduction            : 0.09
% 2.11/1.27  Demodulation         : 0.07
% 2.11/1.27  BG Simplification    : 0.01
% 2.11/1.28  Subsumption          : 0.03
% 2.11/1.28  Abstraction          : 0.02
% 2.11/1.28  MUC search           : 0.00
% 2.11/1.28  Cooper               : 0.00
% 2.11/1.28  Total                : 0.54
% 2.11/1.28  Index Insertion      : 0.00
% 2.11/1.28  Index Deletion       : 0.00
% 2.11/1.28  Index Matching       : 0.00
% 2.11/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
