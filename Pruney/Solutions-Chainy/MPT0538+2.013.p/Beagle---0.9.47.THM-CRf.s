%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_21,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13,c_21])).

tff(c_27,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_10] :
      ( k8_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_27,c_2])).

tff(c_34,plain,(
    ! [A_10] : k8_relat_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_31])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.64/1.08  
% 1.64/1.08  %Foreground sorts:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Background operators:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Foreground operators:
% 1.64/1.08  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.08  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.64/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.08  
% 1.64/1.09  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.64/1.09  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.64/1.09  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.64/1.09  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.64/1.09  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.64/1.09  tff(f_44, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.64/1.09  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.09  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.09  tff(c_13, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.64/1.09  tff(c_21, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.09  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_13, c_21])).
% 1.64/1.09  tff(c_27, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.09  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.09  tff(c_31, plain, (![A_10]: (k8_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_27, c_2])).
% 1.64/1.09  tff(c_34, plain, (![A_10]: (k8_relat_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_31])).
% 1.64/1.09  tff(c_12, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.09  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 1.64/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  Inference rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Ref     : 0
% 1.64/1.09  #Sup     : 4
% 1.64/1.09  #Fact    : 0
% 1.64/1.09  #Define  : 0
% 1.64/1.09  #Split   : 0
% 1.64/1.09  #Chain   : 0
% 1.64/1.09  #Close   : 0
% 1.64/1.09  
% 1.64/1.09  Ordering : KBO
% 1.64/1.09  
% 1.64/1.09  Simplification rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Subsume      : 0
% 1.64/1.09  #Demod        : 3
% 1.64/1.09  #Tautology    : 2
% 1.64/1.09  #SimpNegUnit  : 0
% 1.64/1.09  #BackRed      : 1
% 1.64/1.09  
% 1.64/1.09  #Partial instantiations: 0
% 1.64/1.09  #Strategies tried      : 1
% 1.64/1.09  
% 1.64/1.09  Timing (in seconds)
% 1.64/1.09  ----------------------
% 1.64/1.09  Preprocessing        : 0.26
% 1.64/1.09  Parsing              : 0.14
% 1.64/1.09  CNF conversion       : 0.01
% 1.64/1.09  Main loop            : 0.08
% 1.64/1.09  Inferencing          : 0.04
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.02
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.01
% 1.64/1.09  Abstraction          : 0.00
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.09  Cooper               : 0.00
% 1.64/1.09  Total                : 0.36
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
