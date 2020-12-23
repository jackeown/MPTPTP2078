%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  31 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13,plain,(
    ! [A_9] :
      ( k7_relat_1(A_9,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17,plain,(
    ! [A_2] : k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_25,plain,(
    ! [C_11,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_11,A_12),B_13) = k7_relat_1(C_11,A_12)
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_2,B_13] :
      ( k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k7_relat_1(k1_xboole_0,B_13)
      | ~ r1_tarski(k1_xboole_0,B_13)
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_25])).

tff(c_44,plain,(
    ! [B_13] : k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_17,c_40])).

tff(c_10,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  
% 1.58/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.58/1.05  
% 1.58/1.05  %Foreground sorts:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Background operators:
% 1.58/1.05  
% 1.58/1.05  
% 1.58/1.05  %Foreground operators:
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.58/1.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.58/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.05  
% 1.58/1.06  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.58/1.06  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.58/1.06  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.58/1.06  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.58/1.06  tff(f_42, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.58/1.06  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.06  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.06  tff(c_13, plain, (![A_9]: (k7_relat_1(A_9, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.06  tff(c_17, plain, (![A_2]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.58/1.06  tff(c_25, plain, (![C_11, A_12, B_13]: (k7_relat_1(k7_relat_1(C_11, A_12), B_13)=k7_relat_1(C_11, A_12) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.58/1.06  tff(c_40, plain, (![A_2, B_13]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k7_relat_1(k1_xboole_0, B_13) | ~r1_tarski(k1_xboole_0, B_13) | ~v1_relat_1(k6_relat_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_17, c_25])).
% 1.58/1.06  tff(c_44, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_17, c_40])).
% 1.58/1.06  tff(c_10, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.06  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 1.58/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  Inference rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Ref     : 0
% 1.58/1.06  #Sup     : 8
% 1.58/1.06  #Fact    : 0
% 1.58/1.06  #Define  : 0
% 1.58/1.06  #Split   : 0
% 1.58/1.06  #Chain   : 0
% 1.58/1.06  #Close   : 0
% 1.58/1.06  
% 1.58/1.06  Ordering : KBO
% 1.58/1.06  
% 1.58/1.06  Simplification rules
% 1.58/1.06  ----------------------
% 1.58/1.06  #Subsume      : 0
% 1.58/1.06  #Demod        : 4
% 1.58/1.06  #Tautology    : 4
% 1.58/1.06  #SimpNegUnit  : 0
% 1.58/1.06  #BackRed      : 1
% 1.58/1.06  
% 1.58/1.06  #Partial instantiations: 0
% 1.58/1.06  #Strategies tried      : 1
% 1.58/1.06  
% 1.58/1.06  Timing (in seconds)
% 1.58/1.06  ----------------------
% 1.58/1.06  Preprocessing        : 0.23
% 1.58/1.06  Parsing              : 0.13
% 1.58/1.06  CNF conversion       : 0.01
% 1.58/1.06  Main loop            : 0.08
% 1.58/1.06  Inferencing          : 0.04
% 1.58/1.06  Reduction            : 0.02
% 1.58/1.06  Demodulation         : 0.02
% 1.58/1.06  BG Simplification    : 0.01
% 1.58/1.06  Subsumption          : 0.01
% 1.58/1.06  Abstraction          : 0.00
% 1.58/1.06  MUC search           : 0.00
% 1.58/1.06  Cooper               : 0.00
% 1.58/1.06  Total                : 0.34
% 1.58/1.06  Index Insertion      : 0.00
% 1.58/1.07  Index Deletion       : 0.00
% 1.58/1.07  Index Matching       : 0.00
% 1.58/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
