%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_41,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_23,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    ! [B_7,A_8] :
      ( r1_tarski(k10_relat_1(B_7,A_8),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_8] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_8),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_35,plain,(
    ! [A_9] : r1_tarski(k10_relat_1(k1_xboole_0,A_9),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_39,plain,(
    ! [A_9] : k10_relat_1(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_14,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.61/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.12  
% 1.61/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.61/1.13  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.61/1.13  tff(f_41, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.61/1.13  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.61/1.13  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.61/1.13  tff(f_44, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.61/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.61/1.13  tff(c_23, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.13  tff(c_27, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.61/1.13  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.13  tff(c_29, plain, (![B_7, A_8]: (r1_tarski(k10_relat_1(B_7, A_8), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.13  tff(c_32, plain, (![A_8]: (r1_tarski(k10_relat_1(k1_xboole_0, A_8), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.61/1.13  tff(c_35, plain, (![A_9]: (r1_tarski(k10_relat_1(k1_xboole_0, A_9), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_32])).
% 1.61/1.13  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.61/1.13  tff(c_39, plain, (![A_9]: (k10_relat_1(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_4])).
% 1.61/1.13  tff(c_14, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.13  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_14])).
% 1.61/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  Inference rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Ref     : 0
% 1.61/1.13  #Sup     : 7
% 1.61/1.13  #Fact    : 0
% 1.61/1.13  #Define  : 0
% 1.61/1.13  #Split   : 0
% 1.61/1.13  #Chain   : 0
% 1.61/1.13  #Close   : 0
% 1.61/1.13  
% 1.61/1.13  Ordering : KBO
% 1.61/1.13  
% 1.61/1.13  Simplification rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Subsume      : 0
% 1.61/1.13  #Demod        : 3
% 1.61/1.13  #Tautology    : 4
% 1.61/1.13  #SimpNegUnit  : 0
% 1.61/1.13  #BackRed      : 2
% 1.61/1.13  
% 1.61/1.13  #Partial instantiations: 0
% 1.61/1.13  #Strategies tried      : 1
% 1.61/1.13  
% 1.61/1.13  Timing (in seconds)
% 1.61/1.13  ----------------------
% 1.72/1.14  Preprocessing        : 0.26
% 1.72/1.14  Parsing              : 0.15
% 1.72/1.14  CNF conversion       : 0.01
% 1.72/1.14  Main loop            : 0.09
% 1.72/1.14  Inferencing          : 0.04
% 1.72/1.14  Reduction            : 0.02
% 1.72/1.14  Demodulation         : 0.02
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.01
% 1.72/1.14  Abstraction          : 0.00
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.37
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
