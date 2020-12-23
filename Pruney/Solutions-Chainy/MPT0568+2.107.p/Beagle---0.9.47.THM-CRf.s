%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_19,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19])).

tff(c_38,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_55,plain,(
    ! [B_10,A_11] :
      ( r1_tarski(k10_relat_1(B_10,A_11),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_11] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_11),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_55])).

tff(c_66,plain,(
    ! [A_12] : r1_tarski(k10_relat_1(k1_xboole_0,A_12),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_12] : k10_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_14,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.14  
% 1.55/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.16  %$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.55/1.16  
% 1.55/1.16  %Foreground sorts:
% 1.55/1.16  
% 1.55/1.16  
% 1.55/1.16  %Background operators:
% 1.55/1.16  
% 1.55/1.16  
% 1.55/1.16  %Foreground operators:
% 1.55/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.55/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.55/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.55/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.55/1.16  
% 1.55/1.16  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.55/1.16  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.55/1.16  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.55/1.16  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.55/1.16  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.55/1.16  tff(f_43, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.55/1.16  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.55/1.16  tff(c_19, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.16  tff(c_21, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_19])).
% 1.55/1.16  tff(c_38, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.16  tff(c_47, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_38])).
% 1.55/1.16  tff(c_55, plain, (![B_10, A_11]: (r1_tarski(k10_relat_1(B_10, A_11), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.55/1.16  tff(c_58, plain, (![A_11]: (r1_tarski(k10_relat_1(k1_xboole_0, A_11), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_47, c_55])).
% 1.55/1.16  tff(c_66, plain, (![A_12]: (r1_tarski(k10_relat_1(k1_xboole_0, A_12), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_21, c_58])).
% 1.55/1.16  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.16  tff(c_70, plain, (![A_12]: (k10_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_2])).
% 1.55/1.16  tff(c_14, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.55/1.16  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_14])).
% 1.55/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.16  
% 1.55/1.16  Inference rules
% 1.55/1.16  ----------------------
% 1.55/1.16  #Ref     : 0
% 1.55/1.16  #Sup     : 16
% 1.55/1.16  #Fact    : 0
% 1.55/1.16  #Define  : 0
% 1.55/1.16  #Split   : 0
% 1.55/1.16  #Chain   : 0
% 1.55/1.16  #Close   : 0
% 1.55/1.16  
% 1.55/1.16  Ordering : KBO
% 1.55/1.16  
% 1.55/1.16  Simplification rules
% 1.55/1.16  ----------------------
% 1.55/1.16  #Subsume      : 0
% 1.55/1.16  #Demod        : 4
% 1.55/1.16  #Tautology    : 10
% 1.55/1.16  #SimpNegUnit  : 0
% 1.55/1.16  #BackRed      : 2
% 1.55/1.16  
% 1.55/1.17  #Partial instantiations: 0
% 1.55/1.17  #Strategies tried      : 1
% 1.55/1.17  
% 1.55/1.17  Timing (in seconds)
% 1.55/1.17  ----------------------
% 1.55/1.17  Preprocessing        : 0.26
% 1.55/1.17  Parsing              : 0.15
% 1.55/1.17  CNF conversion       : 0.02
% 1.55/1.17  Main loop            : 0.08
% 1.55/1.17  Inferencing          : 0.03
% 1.55/1.17  Reduction            : 0.02
% 1.55/1.17  Demodulation         : 0.02
% 1.55/1.17  BG Simplification    : 0.01
% 1.55/1.17  Subsumption          : 0.01
% 1.55/1.17  Abstraction          : 0.00
% 1.55/1.17  MUC search           : 0.00
% 1.55/1.17  Cooper               : 0.00
% 1.55/1.17  Total                : 0.37
% 1.55/1.17  Index Insertion      : 0.00
% 1.55/1.17  Index Deletion       : 0.00
% 1.55/1.17  Index Matching       : 0.00
% 1.55/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
