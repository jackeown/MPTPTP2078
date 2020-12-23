%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:04 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_10] :
      ( k7_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_2] : k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_27])).

tff(c_39,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_39])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [B_14,A_15] :
      ( k7_relat_1(B_14,A_15) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_58,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2,c_56])).

tff(c_16,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:28:25 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.09  
% 1.61/1.09  %Foreground sorts:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Background operators:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Foreground operators:
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.09  
% 1.61/1.10  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.61/1.10  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.61/1.10  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.61/1.10  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.61/1.10  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.61/1.10  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.10  tff(f_49, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.61/1.10  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.10  tff(c_27, plain, (![A_10]: (k7_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.10  tff(c_31, plain, (![A_2]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_27])).
% 1.61/1.10  tff(c_39, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.10  tff(c_45, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_39])).
% 1.61/1.10  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_45])).
% 1.61/1.10  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.10  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.10  tff(c_53, plain, (![B_14, A_15]: (k7_relat_1(B_14, A_15)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.10  tff(c_56, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_15) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_53])).
% 1.61/1.10  tff(c_58, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2, c_56])).
% 1.61/1.10  tff(c_16, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.61/1.10  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 1.61/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  Inference rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Ref     : 0
% 1.61/1.10  #Sup     : 11
% 1.61/1.10  #Fact    : 0
% 1.61/1.10  #Define  : 0
% 1.61/1.10  #Split   : 0
% 1.61/1.10  #Chain   : 0
% 1.61/1.10  #Close   : 0
% 1.61/1.10  
% 1.61/1.10  Ordering : KBO
% 1.61/1.10  
% 1.61/1.10  Simplification rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Subsume      : 0
% 1.61/1.10  #Demod        : 4
% 1.61/1.10  #Tautology    : 6
% 1.61/1.10  #SimpNegUnit  : 0
% 1.61/1.10  #BackRed      : 1
% 1.61/1.10  
% 1.61/1.10  #Partial instantiations: 0
% 1.61/1.10  #Strategies tried      : 1
% 1.61/1.10  
% 1.61/1.10  Timing (in seconds)
% 1.61/1.10  ----------------------
% 1.61/1.10  Preprocessing        : 0.25
% 1.61/1.10  Parsing              : 0.14
% 1.61/1.10  CNF conversion       : 0.01
% 1.61/1.10  Main loop            : 0.09
% 1.61/1.10  Inferencing          : 0.04
% 1.61/1.10  Reduction            : 0.02
% 1.61/1.10  Demodulation         : 0.02
% 1.61/1.10  BG Simplification    : 0.01
% 1.61/1.10  Subsumption          : 0.01
% 1.61/1.10  Abstraction          : 0.00
% 1.61/1.10  MUC search           : 0.00
% 1.61/1.10  Cooper               : 0.00
% 1.61/1.10  Total                : 0.37
% 1.61/1.10  Index Insertion      : 0.00
% 1.61/1.10  Index Deletion       : 0.00
% 1.61/1.10  Index Matching       : 0.00
% 1.61/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
