%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:26 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_47,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_54,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18,c_50])).

tff(c_82,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k10_relat_1(B_15,A_16),k10_relat_1(B_15,k2_relat_1(B_15)))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_16] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_16),k10_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_82])).

tff(c_102,plain,(
    ! [A_17] : r1_tarski(k10_relat_1(k1_xboole_0,A_17),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_96])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [B_12,A_13] :
      ( B_12 = A_13
      | ~ r1_tarski(B_12,A_13)
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_55])).

tff(c_114,plain,(
    ! [A_17] : k10_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_64])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  %$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.69/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.15  
% 1.69/1.15  tff(f_47, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.69/1.15  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.69/1.15  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.69/1.15  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.69/1.15  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 1.69/1.15  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.69/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.15  tff(f_50, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.69/1.15  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.69/1.15  tff(c_34, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.15  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_34])).
% 1.69/1.15  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.15  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.15  tff(c_41, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.15  tff(c_50, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_41])).
% 1.69/1.15  tff(c_54, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18, c_50])).
% 1.69/1.15  tff(c_82, plain, (![B_15, A_16]: (r1_tarski(k10_relat_1(B_15, A_16), k10_relat_1(B_15, k2_relat_1(B_15))) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.15  tff(c_96, plain, (![A_16]: (r1_tarski(k10_relat_1(k1_xboole_0, A_16), k10_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_82])).
% 1.69/1.15  tff(c_102, plain, (![A_17]: (r1_tarski(k10_relat_1(k1_xboole_0, A_17), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_96])).
% 1.69/1.15  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.15  tff(c_55, plain, (![B_12, A_13]: (B_12=A_13 | ~r1_tarski(B_12, A_13) | ~r1_tarski(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.15  tff(c_64, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_55])).
% 1.69/1.15  tff(c_114, plain, (![A_17]: (k10_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_64])).
% 1.69/1.15  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.15  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_22])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 25
% 1.69/1.16  #Fact    : 0
% 1.69/1.16  #Define  : 0
% 1.69/1.16  #Split   : 0
% 1.69/1.16  #Chain   : 0
% 1.69/1.16  #Close   : 0
% 1.69/1.16  
% 1.69/1.16  Ordering : KBO
% 1.69/1.16  
% 1.69/1.16  Simplification rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Subsume      : 0
% 1.69/1.16  #Demod        : 18
% 1.69/1.16  #Tautology    : 19
% 1.69/1.16  #SimpNegUnit  : 0
% 1.69/1.16  #BackRed      : 2
% 1.69/1.16  
% 1.69/1.16  #Partial instantiations: 0
% 1.69/1.16  #Strategies tried      : 1
% 1.69/1.16  
% 1.69/1.16  Timing (in seconds)
% 1.69/1.16  ----------------------
% 1.69/1.16  Preprocessing        : 0.27
% 1.69/1.16  Parsing              : 0.14
% 1.69/1.16  CNF conversion       : 0.02
% 1.69/1.16  Main loop            : 0.12
% 1.69/1.16  Inferencing          : 0.05
% 1.69/1.16  Reduction            : 0.04
% 1.69/1.16  Demodulation         : 0.03
% 1.69/1.16  BG Simplification    : 0.01
% 1.69/1.16  Subsumption          : 0.02
% 1.69/1.16  Abstraction          : 0.01
% 1.69/1.16  MUC search           : 0.00
% 1.69/1.16  Cooper               : 0.00
% 1.69/1.16  Total                : 0.41
% 1.69/1.16  Index Insertion      : 0.00
% 1.69/1.16  Index Deletion       : 0.00
% 1.69/1.16  Index Matching       : 0.00
% 1.69/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
