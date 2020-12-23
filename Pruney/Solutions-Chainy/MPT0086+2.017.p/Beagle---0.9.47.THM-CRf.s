%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:15 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  28 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_99,plain,(
    ! [A_24,B_25,C_26] : k4_xboole_0(k4_xboole_0(A_24,B_25),C_26) = k4_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_116,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(B_25,k4_xboole_0(A_24,B_25))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_42])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [A_24,B_25,B_12] : k4_xboole_0(A_24,k2_xboole_0(B_25,k4_xboole_0(k4_xboole_0(A_24,B_25),B_12))) = k3_xboole_0(k4_xboole_0(A_24,B_25),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_3480,plain,(
    ! [A_103,B_104,B_105] : k4_xboole_0(A_103,k2_xboole_0(B_104,k4_xboole_0(A_103,k2_xboole_0(B_104,B_105)))) = k3_xboole_0(k4_xboole_0(A_103,B_104),B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_137])).

tff(c_3697,plain,(
    ! [A_103,A_3] : k4_xboole_0(A_103,k2_xboole_0(A_3,k4_xboole_0(A_103,A_3))) = k3_xboole_0(k4_xboole_0(A_103,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3480])).

tff(c_3746,plain,(
    ! [A_103,A_3] : k3_xboole_0(k4_xboole_0(A_103,A_3),A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_3697])).

tff(c_63,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_16])).

tff(c_3749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:27:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.63  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.47/1.63  
% 3.47/1.63  %Foreground sorts:
% 3.47/1.63  
% 3.47/1.63  
% 3.47/1.63  %Background operators:
% 3.47/1.63  
% 3.47/1.63  
% 3.47/1.63  %Foreground operators:
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.47/1.63  
% 3.88/1.63  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.88/1.63  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.88/1.63  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.88/1.63  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.88/1.63  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.88/1.63  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.88/1.63  tff(c_99, plain, (![A_24, B_25, C_26]: (k4_xboole_0(k4_xboole_0(A_24, B_25), C_26)=k4_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.63  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.63  tff(c_35, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.63  tff(c_42, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 3.88/1.63  tff(c_116, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(B_25, k4_xboole_0(A_24, B_25)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_42])).
% 3.88/1.63  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.63  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.63  tff(c_137, plain, (![A_24, B_25, B_12]: (k4_xboole_0(A_24, k2_xboole_0(B_25, k4_xboole_0(k4_xboole_0(A_24, B_25), B_12)))=k3_xboole_0(k4_xboole_0(A_24, B_25), B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 3.88/1.63  tff(c_3480, plain, (![A_103, B_104, B_105]: (k4_xboole_0(A_103, k2_xboole_0(B_104, k4_xboole_0(A_103, k2_xboole_0(B_104, B_105))))=k3_xboole_0(k4_xboole_0(A_103, B_104), B_105))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_137])).
% 3.88/1.63  tff(c_3697, plain, (![A_103, A_3]: (k4_xboole_0(A_103, k2_xboole_0(A_3, k4_xboole_0(A_103, A_3)))=k3_xboole_0(k4_xboole_0(A_103, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3480])).
% 3.88/1.63  tff(c_3746, plain, (![A_103, A_3]: (k3_xboole_0(k4_xboole_0(A_103, A_3), A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_3697])).
% 3.88/1.63  tff(c_63, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.63  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.88/1.63  tff(c_71, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_16])).
% 3.88/1.63  tff(c_3749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3746, c_71])).
% 3.88/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.63  
% 3.88/1.63  Inference rules
% 3.88/1.63  ----------------------
% 3.88/1.63  #Ref     : 0
% 3.88/1.63  #Sup     : 916
% 3.88/1.63  #Fact    : 0
% 3.88/1.63  #Define  : 0
% 3.88/1.63  #Split   : 0
% 3.88/1.63  #Chain   : 0
% 3.88/1.63  #Close   : 0
% 3.88/1.63  
% 3.88/1.63  Ordering : KBO
% 3.88/1.63  
% 3.88/1.63  Simplification rules
% 3.88/1.63  ----------------------
% 3.88/1.63  #Subsume      : 0
% 3.88/1.63  #Demod        : 729
% 3.88/1.63  #Tautology    : 605
% 3.88/1.63  #SimpNegUnit  : 0
% 3.88/1.63  #BackRed      : 1
% 3.88/1.63  
% 3.88/1.63  #Partial instantiations: 0
% 3.88/1.63  #Strategies tried      : 1
% 3.88/1.63  
% 3.88/1.63  Timing (in seconds)
% 3.88/1.64  ----------------------
% 3.88/1.64  Preprocessing        : 0.25
% 3.88/1.64  Parsing              : 0.14
% 3.88/1.64  CNF conversion       : 0.01
% 3.88/1.64  Main loop            : 0.63
% 3.88/1.64  Inferencing          : 0.23
% 3.88/1.64  Reduction            : 0.24
% 3.88/1.64  Demodulation         : 0.19
% 3.88/1.64  BG Simplification    : 0.02
% 3.88/1.64  Subsumption          : 0.09
% 3.88/1.64  Abstraction          : 0.04
% 3.88/1.64  MUC search           : 0.00
% 3.88/1.64  Cooper               : 0.00
% 3.88/1.64  Total                : 0.90
% 3.88/1.64  Index Insertion      : 0.00
% 3.88/1.64  Index Deletion       : 0.00
% 3.88/1.64  Index Matching       : 0.00
% 3.88/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
