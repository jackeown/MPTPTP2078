%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:04 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    ! [A_10] :
      ( k7_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19,plain,(
    ! [A_2] : k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_15])).

tff(c_27,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_27])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_33])).

tff(c_50,plain,(
    ! [B_14,A_15] :
      ( r1_tarski(k7_relat_1(B_14,A_15),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_63,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_12,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  
% 1.61/1.13  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.61/1.13  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.61/1.13  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.61/1.13  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.61/1.13  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.61/1.13  tff(f_46, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.61/1.13  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.13  tff(c_15, plain, (![A_10]: (k7_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.13  tff(c_19, plain, (![A_2]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_15])).
% 1.61/1.13  tff(c_27, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.13  tff(c_33, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_19, c_27])).
% 1.61/1.13  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_33])).
% 1.61/1.13  tff(c_50, plain, (![B_14, A_15]: (r1_tarski(k7_relat_1(B_14, A_15), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.13  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.13  tff(c_54, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_2])).
% 1.61/1.13  tff(c_63, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54])).
% 1.61/1.13  tff(c_12, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.13  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_12])).
% 1.61/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  Inference rules
% 1.61/1.13  ----------------------
% 1.61/1.13  #Ref     : 0
% 1.61/1.13  #Sup     : 21
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
% 1.61/1.13  #Demod        : 15
% 1.61/1.13  #Tautology    : 14
% 1.61/1.13  #SimpNegUnit  : 0
% 1.61/1.13  #BackRed      : 1
% 1.61/1.13  
% 1.61/1.13  #Partial instantiations: 0
% 1.61/1.13  #Strategies tried      : 1
% 1.61/1.13  
% 1.61/1.13  Timing (in seconds)
% 1.61/1.13  ----------------------
% 1.61/1.13  Preprocessing        : 0.24
% 1.61/1.13  Parsing              : 0.13
% 1.61/1.13  CNF conversion       : 0.01
% 1.61/1.13  Main loop            : 0.10
% 1.61/1.13  Inferencing          : 0.05
% 1.61/1.13  Reduction            : 0.03
% 1.61/1.13  Demodulation         : 0.02
% 1.61/1.13  BG Simplification    : 0.01
% 1.61/1.13  Subsumption          : 0.02
% 1.61/1.13  Abstraction          : 0.00
% 1.61/1.13  MUC search           : 0.00
% 1.61/1.13  Cooper               : 0.00
% 1.61/1.13  Total                : 0.36
% 1.61/1.13  Index Insertion      : 0.00
% 1.61/1.13  Index Deletion       : 0.00
% 1.61/1.13  Index Matching       : 0.00
% 1.61/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
