%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:32 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_49,plain,(
    ! [A_39] : v1_relat_1(k6_relat_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_49])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(k10_relat_1(B_53,A_54),k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [A_54] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_54),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_114])).

tff(c_133,plain,(
    ! [A_58] : r1_tarski(k10_relat_1(k1_xboole_0,A_58),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_120])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [A_59] : k4_xboole_0(k10_relat_1(k1_xboole_0,A_59),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_104,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_143,plain,(
    ! [A_59] : k10_relat_1(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_104])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.19  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.00/1.19  
% 2.00/1.19  %Foreground sorts:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Background operators:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Foreground operators:
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.19  
% 2.00/1.20  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.00/1.20  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.00/1.20  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.20  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.00/1.20  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.00/1.20  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.00/1.20  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.00/1.20  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.00/1.20  tff(f_62, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.00/1.20  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.20  tff(c_49, plain, (![A_39]: (v1_relat_1(k6_relat_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.20  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_49])).
% 2.00/1.20  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.20  tff(c_114, plain, (![B_53, A_54]: (r1_tarski(k10_relat_1(B_53, A_54), k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.20  tff(c_120, plain, (![A_54]: (r1_tarski(k10_relat_1(k1_xboole_0, A_54), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_114])).
% 2.00/1.20  tff(c_133, plain, (![A_58]: (r1_tarski(k10_relat_1(k1_xboole_0, A_58), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_120])).
% 2.00/1.20  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.20  tff(c_138, plain, (![A_59]: (k4_xboole_0(k10_relat_1(k1_xboole_0, A_59), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_4])).
% 2.00/1.20  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.20  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.20  tff(c_92, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.20  tff(c_101, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_92])).
% 2.00/1.20  tff(c_104, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_101])).
% 2.00/1.20  tff(c_143, plain, (![A_59]: (k10_relat_1(k1_xboole_0, A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_104])).
% 2.00/1.20  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.20  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_36])).
% 2.00/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  Inference rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Ref     : 0
% 2.00/1.20  #Sup     : 30
% 2.00/1.20  #Fact    : 0
% 2.00/1.20  #Define  : 0
% 2.00/1.20  #Split   : 0
% 2.00/1.20  #Chain   : 0
% 2.00/1.20  #Close   : 0
% 2.00/1.20  
% 2.00/1.20  Ordering : KBO
% 2.00/1.20  
% 2.00/1.20  Simplification rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Subsume      : 0
% 2.00/1.20  #Demod        : 6
% 2.00/1.20  #Tautology    : 24
% 2.00/1.20  #SimpNegUnit  : 0
% 2.00/1.20  #BackRed      : 3
% 2.00/1.20  
% 2.00/1.20  #Partial instantiations: 0
% 2.00/1.20  #Strategies tried      : 1
% 2.00/1.20  
% 2.00/1.20  Timing (in seconds)
% 2.00/1.20  ----------------------
% 2.00/1.21  Preprocessing        : 0.32
% 2.00/1.21  Parsing              : 0.18
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.12
% 2.00/1.21  Inferencing          : 0.05
% 2.00/1.21  Reduction            : 0.04
% 2.00/1.21  Demodulation         : 0.03
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.01
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.48
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
