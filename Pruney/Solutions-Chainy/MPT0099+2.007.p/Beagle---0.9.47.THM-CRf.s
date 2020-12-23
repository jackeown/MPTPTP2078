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
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_33])).

tff(c_126,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) = k5_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [B_26] : k5_xboole_0(B_26,B_26) = k4_xboole_0(B_26,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_4])).

tff(c_172,plain,(
    ! [B_26] : k5_xboole_0(B_26,B_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_139])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.80/1.18  
% 1.80/1.18  %Foreground sorts:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Background operators:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Foreground operators:
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.80/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.18  
% 1.80/1.18  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.80/1.18  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.80/1.18  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.80/1.18  tff(f_40, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.80/1.18  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.18  tff(c_33, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.18  tff(c_40, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_33])).
% 1.80/1.18  tff(c_126, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25))=k5_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.18  tff(c_139, plain, (![B_26]: (k5_xboole_0(B_26, B_26)=k4_xboole_0(B_26, B_26))), inference(superposition, [status(thm), theory('equality')], [c_126, c_4])).
% 1.80/1.18  tff(c_172, plain, (![B_26]: (k5_xboole_0(B_26, B_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_139])).
% 1.80/1.18  tff(c_14, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.18  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_14])).
% 1.80/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  Inference rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Ref     : 0
% 1.80/1.18  #Sup     : 41
% 1.80/1.18  #Fact    : 0
% 1.80/1.18  #Define  : 0
% 1.80/1.18  #Split   : 0
% 1.80/1.18  #Chain   : 0
% 1.80/1.18  #Close   : 0
% 1.80/1.18  
% 1.80/1.18  Ordering : KBO
% 1.80/1.18  
% 1.80/1.18  Simplification rules
% 1.80/1.18  ----------------------
% 1.80/1.18  #Subsume      : 0
% 1.80/1.18  #Demod        : 11
% 1.80/1.18  #Tautology    : 23
% 1.80/1.18  #SimpNegUnit  : 0
% 1.80/1.18  #BackRed      : 1
% 1.80/1.18  
% 1.80/1.18  #Partial instantiations: 0
% 1.80/1.18  #Strategies tried      : 1
% 1.80/1.18  
% 1.80/1.18  Timing (in seconds)
% 1.80/1.18  ----------------------
% 1.86/1.19  Preprocessing        : 0.27
% 1.86/1.19  Parsing              : 0.15
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.13
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.42
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
