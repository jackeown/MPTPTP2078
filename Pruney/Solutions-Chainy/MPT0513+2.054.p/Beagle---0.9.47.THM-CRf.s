%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  53 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  56 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25])).

tff(c_57,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_57])).

tff(c_73,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_93,plain,(
    ! [C_14,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_14,A_15),B_16) = k7_relat_1(C_14,A_15)
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [B_16] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_16)
      | ~ r1_tarski(k1_xboole_0,B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_93])).

tff(c_129,plain,(
    ! [B_16] : k7_relat_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_73,c_115])).

tff(c_16,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.31  % Computer   : n009.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % DateTime   : Tue Dec  1 14:19:26 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.15/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.07  
% 1.53/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.08  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.53/1.08  
% 1.53/1.08  %Foreground sorts:
% 1.53/1.08  
% 1.53/1.08  
% 1.53/1.08  %Background operators:
% 1.53/1.08  
% 1.53/1.08  
% 1.53/1.08  %Foreground operators:
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.53/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.53/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.53/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.53/1.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.53/1.08  
% 1.67/1.08  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.67/1.08  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.67/1.08  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.67/1.08  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.67/1.08  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.67/1.08  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.67/1.08  tff(f_47, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.67/1.09  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.09  tff(c_22, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.09  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_22])).
% 1.67/1.09  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.09  tff(c_25, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.09  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_25])).
% 1.67/1.09  tff(c_57, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.09  tff(c_66, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_57])).
% 1.67/1.09  tff(c_73, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 1.67/1.09  tff(c_93, plain, (![C_14, A_15, B_16]: (k7_relat_1(k7_relat_1(C_14, A_15), B_16)=k7_relat_1(C_14, A_15) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.09  tff(c_115, plain, (![B_16]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_16) | ~r1_tarski(k1_xboole_0, B_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_73, c_93])).
% 1.67/1.09  tff(c_129, plain, (![B_16]: (k7_relat_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_73, c_115])).
% 1.67/1.09  tff(c_16, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.09  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_16])).
% 1.67/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  Inference rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Ref     : 0
% 1.67/1.09  #Sup     : 31
% 1.67/1.09  #Fact    : 0
% 1.67/1.09  #Define  : 0
% 1.67/1.09  #Split   : 0
% 1.67/1.09  #Chain   : 0
% 1.67/1.09  #Close   : 0
% 1.67/1.09  
% 1.67/1.09  Ordering : KBO
% 1.67/1.09  
% 1.67/1.09  Simplification rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Subsume      : 0
% 1.67/1.09  #Demod        : 11
% 1.67/1.09  #Tautology    : 22
% 1.67/1.09  #SimpNegUnit  : 0
% 1.67/1.09  #BackRed      : 1
% 1.67/1.09  
% 1.67/1.09  #Partial instantiations: 0
% 1.67/1.09  #Strategies tried      : 1
% 1.67/1.09  
% 1.67/1.09  Timing (in seconds)
% 1.67/1.09  ----------------------
% 1.67/1.09  Preprocessing        : 0.25
% 1.67/1.09  Parsing              : 0.14
% 1.67/1.09  CNF conversion       : 0.01
% 1.67/1.09  Main loop            : 0.12
% 1.67/1.09  Inferencing          : 0.05
% 1.67/1.09  Reduction            : 0.03
% 1.67/1.09  Demodulation         : 0.03
% 1.67/1.09  BG Simplification    : 0.01
% 1.67/1.09  Subsumption          : 0.01
% 1.67/1.09  Abstraction          : 0.01
% 1.67/1.09  MUC search           : 0.00
% 1.67/1.09  Cooper               : 0.00
% 1.67/1.09  Total                : 0.39
% 1.67/1.09  Index Insertion      : 0.00
% 1.67/1.09  Index Deletion       : 0.00
% 1.67/1.09  Index Matching       : 0.00
% 1.67/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
