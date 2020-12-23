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
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_subset_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_41,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_28,plain,(
    ! [A_8] :
      ( v1_xboole_0(k4_relat_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_9] :
      ( k4_relat_1(A_9) = k1_xboole_0
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_39,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13,c_33])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:33:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.08  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_subset_1 > k1_xboole_0
% 1.59/1.08  
% 1.59/1.08  %Foreground sorts:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Background operators:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Foreground operators:
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.08  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.59/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.08  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.59/1.08  
% 1.59/1.09  tff(f_41, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.59/1.09  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.59/1.09  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.59/1.09  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.59/1.09  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.59/1.09  tff(c_12, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.59/1.09  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.09  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.09  tff(c_13, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.59/1.09  tff(c_28, plain, (![A_8]: (v1_xboole_0(k4_relat_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.59/1.09  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.09  tff(c_33, plain, (![A_9]: (k4_relat_1(A_9)=k1_xboole_0 | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_28, c_2])).
% 1.59/1.09  tff(c_39, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_13, c_33])).
% 1.59/1.09  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_39])).
% 1.59/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  Inference rules
% 1.59/1.09  ----------------------
% 1.59/1.09  #Ref     : 0
% 1.59/1.09  #Sup     : 6
% 1.59/1.09  #Fact    : 0
% 1.59/1.09  #Define  : 0
% 1.59/1.09  #Split   : 0
% 1.59/1.09  #Chain   : 0
% 1.59/1.09  #Close   : 0
% 1.59/1.09  
% 1.59/1.09  Ordering : KBO
% 1.59/1.09  
% 1.59/1.09  Simplification rules
% 1.59/1.09  ----------------------
% 1.59/1.09  #Subsume      : 0
% 1.59/1.09  #Demod        : 1
% 1.59/1.09  #Tautology    : 3
% 1.59/1.09  #SimpNegUnit  : 1
% 1.59/1.09  #BackRed      : 0
% 1.59/1.09  
% 1.59/1.09  #Partial instantiations: 0
% 1.59/1.09  #Strategies tried      : 1
% 1.59/1.09  
% 1.59/1.09  Timing (in seconds)
% 1.59/1.09  ----------------------
% 1.59/1.10  Preprocessing        : 0.24
% 1.59/1.10  Parsing              : 0.13
% 1.59/1.10  CNF conversion       : 0.01
% 1.59/1.10  Main loop            : 0.08
% 1.59/1.10  Inferencing          : 0.04
% 1.59/1.10  Reduction            : 0.02
% 1.59/1.10  Demodulation         : 0.01
% 1.59/1.10  BG Simplification    : 0.01
% 1.59/1.10  Subsumption          : 0.01
% 1.59/1.10  Abstraction          : 0.00
% 1.59/1.10  MUC search           : 0.00
% 1.59/1.10  Cooper               : 0.00
% 1.59/1.10  Total                : 0.35
% 1.59/1.10  Index Insertion      : 0.00
% 1.59/1.10  Index Deletion       : 0.00
% 1.59/1.10  Index Matching       : 0.00
% 1.59/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
