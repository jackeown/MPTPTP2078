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
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [B_9,A_10] :
      ( r1_xboole_0(B_9,A_10)
      | ~ r1_xboole_0(A_10,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [B_14,A_15] :
      ( k7_relat_1(B_14,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_14),A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_67,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38,c_63])).

tff(c_18,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n014.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 12:03:22 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.04  
% 1.62/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.04  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.62/1.04  
% 1.62/1.04  %Foreground sorts:
% 1.62/1.04  
% 1.62/1.04  
% 1.62/1.04  %Background operators:
% 1.62/1.04  
% 1.62/1.04  
% 1.62/1.04  %Foreground operators:
% 1.62/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.04  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.62/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.62/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.04  
% 1.62/1.05  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.62/1.05  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.62/1.05  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.62/1.05  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.62/1.05  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.62/1.05  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.62/1.05  tff(f_46, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.62/1.05  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.05  tff(c_28, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.05  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_28])).
% 1.62/1.05  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.05  tff(c_35, plain, (![B_9, A_10]: (r1_xboole_0(B_9, A_10) | ~r1_xboole_0(A_10, B_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.05  tff(c_38, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_4, c_35])).
% 1.62/1.05  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.05  tff(c_53, plain, (![B_14, A_15]: (k7_relat_1(B_14, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_14), A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.05  tff(c_63, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_15) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 1.62/1.05  tff(c_67, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38, c_63])).
% 1.62/1.05  tff(c_18, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.05  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_18])).
% 1.62/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.05  
% 1.62/1.05  Inference rules
% 1.62/1.05  ----------------------
% 1.62/1.05  #Ref     : 0
% 1.62/1.05  #Sup     : 14
% 1.62/1.05  #Fact    : 0
% 1.62/1.05  #Define  : 0
% 1.62/1.05  #Split   : 0
% 1.62/1.05  #Chain   : 0
% 1.62/1.05  #Close   : 0
% 1.62/1.05  
% 1.62/1.05  Ordering : KBO
% 1.62/1.05  
% 1.62/1.05  Simplification rules
% 1.62/1.05  ----------------------
% 1.62/1.05  #Subsume      : 0
% 1.62/1.05  #Demod        : 6
% 1.62/1.05  #Tautology    : 9
% 1.62/1.05  #SimpNegUnit  : 0
% 1.62/1.05  #BackRed      : 1
% 1.62/1.05  
% 1.62/1.05  #Partial instantiations: 0
% 1.62/1.05  #Strategies tried      : 1
% 1.62/1.05  
% 1.62/1.05  Timing (in seconds)
% 1.62/1.05  ----------------------
% 1.62/1.05  Preprocessing        : 0.27
% 1.62/1.05  Parsing              : 0.15
% 1.62/1.05  CNF conversion       : 0.02
% 1.62/1.05  Main loop            : 0.11
% 1.62/1.05  Inferencing          : 0.05
% 1.62/1.05  Reduction            : 0.03
% 1.62/1.05  Demodulation         : 0.02
% 1.62/1.05  BG Simplification    : 0.01
% 1.62/1.05  Subsumption          : 0.02
% 1.62/1.05  Abstraction          : 0.00
% 1.62/1.05  MUC search           : 0.00
% 1.62/1.05  Cooper               : 0.00
% 1.62/1.05  Total                : 0.40
% 1.62/1.05  Index Insertion      : 0.00
% 1.62/1.05  Index Deletion       : 0.00
% 1.62/1.05  Index Matching       : 0.00
% 1.62/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
