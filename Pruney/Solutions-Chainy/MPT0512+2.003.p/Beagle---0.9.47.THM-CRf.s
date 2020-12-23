%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:57 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_29,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k7_relat_1(A_8,B_9))
      | ~ v1_xboole_0(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_12,B_13] :
      ( k7_relat_1(A_12,B_13) = k1_xboole_0
      | ~ v1_xboole_0(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_29,c_2])).

tff(c_42,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_15,c_35])).

tff(c_48,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.47  
% 2.02/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.48  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.02/1.48  
% 2.02/1.48  %Foreground sorts:
% 2.02/1.48  
% 2.02/1.48  
% 2.02/1.48  %Background operators:
% 2.02/1.48  
% 2.02/1.48  
% 2.02/1.48  %Foreground operators:
% 2.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.02/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.48  
% 2.02/1.49  tff(f_46, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.02/1.49  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.02/1.49  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.02/1.49  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.02/1.49  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.49  tff(c_12, plain, (k7_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.49  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.49  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.49  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.49  tff(c_15, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.02/1.49  tff(c_29, plain, (![A_8, B_9]: (v1_xboole_0(k7_relat_1(A_8, B_9)) | ~v1_xboole_0(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.49  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.49  tff(c_35, plain, (![A_12, B_13]: (k7_relat_1(A_12, B_13)=k1_xboole_0 | ~v1_xboole_0(B_13) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_29, c_2])).
% 2.02/1.49  tff(c_42, plain, (![A_14]: (k7_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_15, c_35])).
% 2.02/1.49  tff(c_48, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_42])).
% 2.02/1.49  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_48])).
% 2.02/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.49  
% 2.02/1.49  Inference rules
% 2.02/1.49  ----------------------
% 2.02/1.49  #Ref     : 0
% 2.02/1.49  #Sup     : 8
% 2.02/1.49  #Fact    : 0
% 2.02/1.49  #Define  : 0
% 2.02/1.49  #Split   : 0
% 2.02/1.49  #Chain   : 0
% 2.02/1.49  #Close   : 0
% 2.02/1.49  
% 2.02/1.49  Ordering : KBO
% 2.02/1.49  
% 2.02/1.49  Simplification rules
% 2.02/1.49  ----------------------
% 2.02/1.49  #Subsume      : 0
% 2.02/1.49  #Demod        : 1
% 2.02/1.49  #Tautology    : 3
% 2.02/1.49  #SimpNegUnit  : 1
% 2.02/1.49  #BackRed      : 0
% 2.02/1.49  
% 2.02/1.49  #Partial instantiations: 0
% 2.02/1.49  #Strategies tried      : 1
% 2.02/1.49  
% 2.02/1.49  Timing (in seconds)
% 2.02/1.49  ----------------------
% 2.02/1.50  Preprocessing        : 0.39
% 2.02/1.50  Parsing              : 0.21
% 2.02/1.50  CNF conversion       : 0.02
% 2.02/1.50  Main loop            : 0.16
% 2.02/1.50  Inferencing          : 0.07
% 2.02/1.50  Reduction            : 0.04
% 2.02/1.50  Demodulation         : 0.03
% 2.02/1.50  BG Simplification    : 0.01
% 2.02/1.50  Subsumption          : 0.03
% 2.02/1.50  Abstraction          : 0.01
% 2.02/1.50  MUC search           : 0.00
% 2.02/1.50  Cooper               : 0.00
% 2.02/1.50  Total                : 0.58
% 2.02/1.50  Index Insertion      : 0.00
% 2.02/1.50  Index Deletion       : 0.00
% 2.02/1.50  Index Matching       : 0.00
% 2.02/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
