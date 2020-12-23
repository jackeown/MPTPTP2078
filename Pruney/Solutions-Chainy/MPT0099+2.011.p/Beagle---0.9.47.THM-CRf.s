%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:37 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_236,plain,(
    ! [A_23,B_24] : k2_xboole_0(k4_xboole_0(A_23,B_24),k4_xboole_0(B_24,A_23)) = k5_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_246,plain,(
    ! [B_24] : k5_xboole_0(B_24,B_24) = k4_xboole_0(B_24,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_4])).

tff(c_297,plain,(
    ! [B_24] : k5_xboole_0(B_24,B_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_246])).

tff(c_12,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.17  
% 1.86/1.17  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.86/1.17  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.86/1.17  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.86/1.17  tff(f_38, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.86/1.17  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.17  tff(c_31, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.17  tff(c_38, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 1.86/1.17  tff(c_236, plain, (![A_23, B_24]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k4_xboole_0(B_24, A_23))=k5_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.17  tff(c_246, plain, (![B_24]: (k5_xboole_0(B_24, B_24)=k4_xboole_0(B_24, B_24))), inference(superposition, [status(thm), theory('equality')], [c_236, c_4])).
% 1.86/1.17  tff(c_297, plain, (![B_24]: (k5_xboole_0(B_24, B_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_246])).
% 1.86/1.17  tff(c_12, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.17  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_12])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 72
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 0
% 1.86/1.17  #Demod        : 37
% 1.86/1.17  #Tautology    : 35
% 1.86/1.17  #SimpNegUnit  : 0
% 1.86/1.17  #BackRed      : 1
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.18  Preprocessing        : 0.25
% 1.86/1.18  Parsing              : 0.14
% 1.86/1.18  CNF conversion       : 0.01
% 1.86/1.18  Main loop            : 0.16
% 1.86/1.18  Inferencing          : 0.06
% 1.86/1.18  Reduction            : 0.06
% 1.86/1.18  Demodulation         : 0.05
% 1.86/1.18  BG Simplification    : 0.01
% 1.86/1.18  Subsumption          : 0.02
% 1.86/1.18  Abstraction          : 0.01
% 1.86/1.18  MUC search           : 0.00
% 1.86/1.18  Cooper               : 0.00
% 1.86/1.18  Total                : 0.43
% 1.86/1.18  Index Insertion      : 0.00
% 1.86/1.18  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
