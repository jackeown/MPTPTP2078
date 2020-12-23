%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  27 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_40,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_52,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_144,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k4_xboole_0(A_21,B_22),C_23) = k4_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_300,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_28)) = k4_xboole_0('#skF_1',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_144])).

tff(c_316,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_28)) = k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_12])).

tff(c_328,plain,(
    ! [C_28] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_28)) = k3_xboole_0('#skF_1',C_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_316])).

tff(c_14,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.26  
% 2.25/1.27  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.25/1.27  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.25/1.27  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.25/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.25/1.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.25/1.27  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.25/1.27  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.27  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.27  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.27  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.27  tff(c_30, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_26])).
% 2.25/1.27  tff(c_40, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.27  tff(c_49, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_40])).
% 2.25/1.27  tff(c_52, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_49])).
% 2.25/1.27  tff(c_144, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k4_xboole_0(A_21, B_22), C_23)=k4_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.27  tff(c_300, plain, (![C_28]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_28))=k4_xboole_0('#skF_1', C_28))), inference(superposition, [status(thm), theory('equality')], [c_52, c_144])).
% 2.25/1.27  tff(c_316, plain, (![C_28]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_28))=k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_28)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_12])).
% 2.25/1.27  tff(c_328, plain, (![C_28]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_28))=k3_xboole_0('#skF_1', C_28))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_316])).
% 2.25/1.27  tff(c_14, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.27  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_328, c_14])).
% 2.25/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  Inference rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Ref     : 0
% 2.25/1.27  #Sup     : 137
% 2.25/1.27  #Fact    : 0
% 2.25/1.27  #Define  : 0
% 2.25/1.27  #Split   : 0
% 2.25/1.27  #Chain   : 0
% 2.25/1.27  #Close   : 0
% 2.25/1.27  
% 2.25/1.27  Ordering : KBO
% 2.25/1.27  
% 2.25/1.27  Simplification rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Subsume      : 0
% 2.25/1.27  #Demod        : 111
% 2.25/1.27  #Tautology    : 86
% 2.25/1.27  #SimpNegUnit  : 0
% 2.25/1.27  #BackRed      : 1
% 2.25/1.27  
% 2.25/1.27  #Partial instantiations: 0
% 2.25/1.27  #Strategies tried      : 1
% 2.25/1.27  
% 2.25/1.27  Timing (in seconds)
% 2.25/1.27  ----------------------
% 2.25/1.27  Preprocessing        : 0.26
% 2.25/1.27  Parsing              : 0.15
% 2.25/1.27  CNF conversion       : 0.01
% 2.25/1.27  Main loop            : 0.26
% 2.25/1.27  Inferencing          : 0.11
% 2.25/1.27  Reduction            : 0.10
% 2.25/1.27  Demodulation         : 0.08
% 2.25/1.27  BG Simplification    : 0.01
% 2.25/1.27  Subsumption          : 0.03
% 2.25/1.27  Abstraction          : 0.02
% 2.25/1.27  MUC search           : 0.00
% 2.25/1.27  Cooper               : 0.00
% 2.25/1.27  Total                : 0.54
% 2.25/1.27  Index Insertion      : 0.00
% 2.25/1.27  Index Deletion       : 0.00
% 2.25/1.27  Index Matching       : 0.00
% 2.25/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
