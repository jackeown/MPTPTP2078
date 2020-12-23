%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:37 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  25 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_56,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_86,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_16] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_16,A_16)) = k5_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2])).

tff(c_109,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_56,c_91])).

tff(c_12,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.15  
% 1.50/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.15  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.50/1.15  
% 1.50/1.15  %Foreground sorts:
% 1.50/1.15  
% 1.50/1.15  
% 1.50/1.15  %Background operators:
% 1.50/1.15  
% 1.50/1.15  
% 1.50/1.15  %Foreground operators:
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.50/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.50/1.15  
% 1.50/1.16  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.50/1.16  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.50/1.16  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.50/1.16  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.50/1.16  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.50/1.16  tff(f_38, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.50/1.16  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.16  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.50/1.16  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.16  tff(c_38, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.50/1.16  tff(c_53, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 1.50/1.16  tff(c_56, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_53])).
% 1.50/1.16  tff(c_86, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_53])).
% 1.50/1.16  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.50/1.16  tff(c_91, plain, (![A_16]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_16, A_16))=k5_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_86, c_2])).
% 1.50/1.16  tff(c_109, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_56, c_91])).
% 1.50/1.16  tff(c_12, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.50/1.16  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_12])).
% 1.50/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.16  
% 1.50/1.16  Inference rules
% 1.50/1.16  ----------------------
% 1.50/1.16  #Ref     : 0
% 1.50/1.16  #Sup     : 26
% 1.50/1.16  #Fact    : 0
% 1.50/1.16  #Define  : 0
% 1.50/1.16  #Split   : 0
% 1.50/1.16  #Chain   : 0
% 1.50/1.16  #Close   : 0
% 1.50/1.16  
% 1.50/1.16  Ordering : KBO
% 1.50/1.16  
% 1.50/1.16  Simplification rules
% 1.50/1.16  ----------------------
% 1.50/1.16  #Subsume      : 0
% 1.50/1.16  #Demod        : 7
% 1.50/1.16  #Tautology    : 14
% 1.50/1.16  #SimpNegUnit  : 0
% 1.50/1.16  #BackRed      : 1
% 1.50/1.16  
% 1.50/1.16  #Partial instantiations: 0
% 1.50/1.16  #Strategies tried      : 1
% 1.50/1.16  
% 1.50/1.16  Timing (in seconds)
% 1.50/1.16  ----------------------
% 1.50/1.16  Preprocessing        : 0.23
% 1.50/1.16  Parsing              : 0.13
% 1.50/1.17  CNF conversion       : 0.01
% 1.50/1.17  Main loop            : 0.10
% 1.50/1.17  Inferencing          : 0.05
% 1.50/1.17  Reduction            : 0.03
% 1.50/1.17  Demodulation         : 0.02
% 1.50/1.17  BG Simplification    : 0.01
% 1.50/1.17  Subsumption          : 0.01
% 1.50/1.17  Abstraction          : 0.01
% 1.50/1.17  MUC search           : 0.00
% 1.50/1.17  Cooper               : 0.00
% 1.50/1.17  Total                : 0.35
% 1.50/1.17  Index Insertion      : 0.00
% 1.50/1.17  Index Deletion       : 0.00
% 1.50/1.17  Index Matching       : 0.00
% 1.50/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
