%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:57 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_10,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_23,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k7_relat_1(A_8,B_9))
      | ~ v1_xboole_0(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13,plain,(
    ! [B_5,A_6] :
      ( ~ v1_xboole_0(B_5)
      | B_5 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( k7_relat_1(A_12,B_13) = k1_xboole_0
      | ~ v1_xboole_0(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_23,c_16])).

tff(c_39,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_45,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.13  
% 1.52/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.13  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.52/1.13  
% 1.52/1.13  %Foreground sorts:
% 1.52/1.13  
% 1.52/1.13  
% 1.52/1.13  %Background operators:
% 1.52/1.13  
% 1.52/1.13  
% 1.52/1.13  %Foreground operators:
% 1.52/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.52/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.52/1.13  
% 1.52/1.14  tff(f_47, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.52/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.52/1.14  tff(f_42, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 1.52/1.14  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.52/1.14  tff(c_10, plain, (k7_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.52/1.14  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.52/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.52/1.14  tff(c_23, plain, (![A_8, B_9]: (v1_xboole_0(k7_relat_1(A_8, B_9)) | ~v1_xboole_0(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.14  tff(c_13, plain, (![B_5, A_6]: (~v1_xboole_0(B_5) | B_5=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.52/1.14  tff(c_16, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2, c_13])).
% 1.52/1.14  tff(c_32, plain, (![A_12, B_13]: (k7_relat_1(A_12, B_13)=k1_xboole_0 | ~v1_xboole_0(B_13) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_23, c_16])).
% 1.52/1.14  tff(c_39, plain, (![A_14]: (k7_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.52/1.14  tff(c_45, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.52/1.14  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_45])).
% 1.52/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.14  
% 1.52/1.14  Inference rules
% 1.52/1.14  ----------------------
% 1.52/1.14  #Ref     : 0
% 1.52/1.14  #Sup     : 8
% 1.52/1.14  #Fact    : 0
% 1.52/1.14  #Define  : 0
% 1.52/1.14  #Split   : 0
% 1.52/1.14  #Chain   : 0
% 1.52/1.14  #Close   : 0
% 1.52/1.14  
% 1.52/1.14  Ordering : KBO
% 1.52/1.14  
% 1.52/1.14  Simplification rules
% 1.52/1.14  ----------------------
% 1.52/1.14  #Subsume      : 0
% 1.52/1.14  #Demod        : 0
% 1.52/1.14  #Tautology    : 1
% 1.52/1.14  #SimpNegUnit  : 1
% 1.52/1.14  #BackRed      : 0
% 1.52/1.14  
% 1.52/1.14  #Partial instantiations: 0
% 1.52/1.14  #Strategies tried      : 1
% 1.52/1.14  
% 1.52/1.14  Timing (in seconds)
% 1.52/1.14  ----------------------
% 1.52/1.14  Preprocessing        : 0.22
% 1.52/1.14  Parsing              : 0.12
% 1.52/1.14  CNF conversion       : 0.01
% 1.52/1.14  Main loop            : 0.09
% 1.52/1.14  Inferencing          : 0.04
% 1.52/1.14  Reduction            : 0.02
% 1.52/1.14  Demodulation         : 0.01
% 1.52/1.14  BG Simplification    : 0.01
% 1.52/1.14  Subsumption          : 0.02
% 1.52/1.14  Abstraction          : 0.00
% 1.52/1.14  MUC search           : 0.00
% 1.52/1.14  Cooper               : 0.00
% 1.52/1.14  Total                : 0.32
% 1.52/1.14  Index Insertion      : 0.00
% 1.52/1.14  Index Deletion       : 0.00
% 1.52/1.14  Index Matching       : 0.00
% 1.52/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
