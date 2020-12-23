%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:45 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  33 expanded)
%              Number of equality atoms :   19 (  21 expanded)
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

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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

tff(c_41,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_41])).

tff(c_54,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [B_12] : k3_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,(
    ! [B_17,A_18] :
      ( k9_relat_1(B_17,k3_xboole_0(k1_relat_1(B_17),A_18)) = k9_relat_1(B_17,A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_18] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_18)) = k9_relat_1(k1_xboole_0,A_18)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_139,plain,(
    ! [A_18] : k9_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_48,c_64,c_135])).

tff(c_18,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:39:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.26  %$ v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.98/1.26  
% 1.98/1.26  %Foreground sorts:
% 1.98/1.26  
% 1.98/1.26  
% 1.98/1.26  %Background operators:
% 1.98/1.26  
% 1.98/1.26  
% 1.98/1.26  %Foreground operators:
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.98/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.26  
% 1.98/1.27  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.98/1.27  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.98/1.27  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 1.98/1.27  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.98/1.27  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.98/1.27  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.27  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 1.98/1.27  tff(f_46, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.98/1.27  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.27  tff(c_31, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.27  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_31])).
% 1.98/1.27  tff(c_41, plain, (![A_10]: (k9_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.27  tff(c_48, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_41])).
% 1.98/1.27  tff(c_54, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.27  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.27  tff(c_64, plain, (![B_12]: (k3_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_4])).
% 1.98/1.27  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.27  tff(c_126, plain, (![B_17, A_18]: (k9_relat_1(B_17, k3_xboole_0(k1_relat_1(B_17), A_18))=k9_relat_1(B_17, A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.27  tff(c_135, plain, (![A_18]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_18))=k9_relat_1(k1_xboole_0, A_18) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_126])).
% 1.98/1.27  tff(c_139, plain, (![A_18]: (k9_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_33, c_48, c_64, c_135])).
% 1.98/1.27  tff(c_18, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.98/1.27  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_18])).
% 1.98/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  Inference rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Ref     : 0
% 1.98/1.27  #Sup     : 34
% 1.98/1.27  #Fact    : 0
% 1.98/1.27  #Define  : 0
% 1.98/1.27  #Split   : 0
% 1.98/1.27  #Chain   : 0
% 1.98/1.27  #Close   : 0
% 1.98/1.27  
% 1.98/1.27  Ordering : KBO
% 1.98/1.27  
% 1.98/1.27  Simplification rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Subsume      : 0
% 1.98/1.27  #Demod        : 16
% 1.98/1.27  #Tautology    : 27
% 1.98/1.27  #SimpNegUnit  : 0
% 1.98/1.27  #BackRed      : 1
% 1.98/1.27  
% 1.98/1.27  #Partial instantiations: 0
% 1.98/1.27  #Strategies tried      : 1
% 1.98/1.27  
% 1.98/1.27  Timing (in seconds)
% 1.98/1.27  ----------------------
% 1.98/1.27  Preprocessing        : 0.31
% 1.98/1.27  Parsing              : 0.16
% 1.98/1.27  CNF conversion       : 0.02
% 1.98/1.27  Main loop            : 0.14
% 1.98/1.27  Inferencing          : 0.06
% 1.98/1.27  Reduction            : 0.04
% 1.98/1.27  Demodulation         : 0.03
% 1.98/1.27  BG Simplification    : 0.01
% 1.98/1.27  Subsumption          : 0.02
% 1.98/1.27  Abstraction          : 0.01
% 1.98/1.27  MUC search           : 0.00
% 1.98/1.27  Cooper               : 0.00
% 1.98/1.27  Total                : 0.48
% 1.98/1.27  Index Insertion      : 0.00
% 1.98/1.27  Index Deletion       : 0.00
% 1.98/1.27  Index Matching       : 0.00
% 1.98/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
