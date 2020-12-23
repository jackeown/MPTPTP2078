%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_31])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_41])).

tff(c_54,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_12,c_50])).

tff(c_59,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [B_12] : k3_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_122,plain,(
    ! [B_16,A_17] :
      ( k9_relat_1(B_16,k3_xboole_0(k1_relat_1(B_16),A_17)) = k9_relat_1(B_16,A_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_17] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_17)) = k9_relat_1(k1_xboole_0,A_17)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_122])).

tff(c_135,plain,(
    ! [A_17] : k9_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_54,c_69,c_131])).

tff(c_18,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.19  
% 1.71/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.19  %$ v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.71/1.19  
% 1.71/1.19  %Foreground sorts:
% 1.71/1.19  
% 1.71/1.19  
% 1.71/1.19  %Background operators:
% 1.71/1.19  
% 1.71/1.19  
% 1.71/1.19  %Foreground operators:
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.71/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.20  
% 1.71/1.20  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.71/1.20  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.71/1.20  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.20  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.71/1.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.71/1.20  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.71/1.20  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 1.71/1.20  tff(f_46, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.71/1.20  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.71/1.20  tff(c_31, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.20  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_31])).
% 1.71/1.20  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.20  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.20  tff(c_41, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.20  tff(c_50, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_41])).
% 1.71/1.20  tff(c_54, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33, c_12, c_50])).
% 1.71/1.20  tff(c_59, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.20  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.20  tff(c_69, plain, (![B_12]: (k3_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 1.71/1.20  tff(c_122, plain, (![B_16, A_17]: (k9_relat_1(B_16, k3_xboole_0(k1_relat_1(B_16), A_17))=k9_relat_1(B_16, A_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.20  tff(c_131, plain, (![A_17]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_17))=k9_relat_1(k1_xboole_0, A_17) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_122])).
% 1.71/1.20  tff(c_135, plain, (![A_17]: (k9_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_33, c_54, c_69, c_131])).
% 1.71/1.20  tff(c_18, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.20  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_18])).
% 1.71/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.20  
% 1.71/1.20  Inference rules
% 1.71/1.20  ----------------------
% 1.71/1.20  #Ref     : 0
% 1.71/1.20  #Sup     : 32
% 1.71/1.20  #Fact    : 0
% 1.71/1.20  #Define  : 0
% 1.71/1.20  #Split   : 0
% 1.71/1.20  #Chain   : 0
% 1.71/1.20  #Close   : 0
% 1.71/1.20  
% 1.71/1.20  Ordering : KBO
% 1.71/1.20  
% 1.71/1.20  Simplification rules
% 1.71/1.20  ----------------------
% 1.71/1.20  #Subsume      : 0
% 1.71/1.20  #Demod        : 18
% 1.71/1.20  #Tautology    : 27
% 1.71/1.20  #SimpNegUnit  : 0
% 1.71/1.20  #BackRed      : 1
% 1.71/1.20  
% 1.71/1.20  #Partial instantiations: 0
% 1.71/1.20  #Strategies tried      : 1
% 1.71/1.20  
% 1.71/1.20  Timing (in seconds)
% 1.71/1.20  ----------------------
% 1.71/1.21  Preprocessing        : 0.28
% 1.71/1.21  Parsing              : 0.15
% 1.71/1.21  CNF conversion       : 0.02
% 1.71/1.21  Main loop            : 0.12
% 1.71/1.21  Inferencing          : 0.06
% 1.71/1.21  Reduction            : 0.04
% 1.71/1.21  Demodulation         : 0.03
% 1.71/1.21  BG Simplification    : 0.01
% 1.71/1.21  Subsumption          : 0.01
% 1.71/1.21  Abstraction          : 0.01
% 1.71/1.21  MUC search           : 0.00
% 1.71/1.21  Cooper               : 0.00
% 1.71/1.21  Total                : 0.42
% 1.71/1.21  Index Insertion      : 0.00
% 1.71/1.21  Index Deletion       : 0.00
% 1.71/1.21  Index Matching       : 0.00
% 1.71/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
