%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_41,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(c_10,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_26])).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [B_6,A_7] :
      ( k5_relat_1(B_6,k6_relat_1(A_7)) = k8_relat_1(A_7,B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_8] :
      ( k8_relat_1(k1_xboole_0,B_8) = k5_relat_1(B_8,k1_xboole_0)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_50,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k5_relat_1('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_52,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  %$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  
% 1.60/1.10  tff(f_41, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 1.60/1.10  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.60/1.10  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.60/1.10  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.60/1.10  tff(c_10, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.10  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.10  tff(c_26, plain, (![A_5]: (k5_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.10  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_26])).
% 1.60/1.10  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.10  tff(c_35, plain, (![B_6, A_7]: (k5_relat_1(B_6, k6_relat_1(A_7))=k8_relat_1(A_7, B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.10  tff(c_47, plain, (![B_8]: (k8_relat_1(k1_xboole_0, B_8)=k5_relat_1(B_8, k1_xboole_0) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_35])).
% 1.60/1.10  tff(c_50, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k5_relat_1('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_47])).
% 1.60/1.10  tff(c_52, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 1.60/1.10  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_52])).
% 1.60/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  Inference rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Ref     : 0
% 1.60/1.10  #Sup     : 12
% 1.60/1.10  #Fact    : 0
% 1.60/1.10  #Define  : 0
% 1.60/1.10  #Split   : 0
% 1.60/1.10  #Chain   : 0
% 1.60/1.10  #Close   : 0
% 1.60/1.10  
% 1.60/1.10  Ordering : KBO
% 1.60/1.10  
% 1.60/1.10  Simplification rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Subsume      : 0
% 1.60/1.10  #Demod        : 1
% 1.60/1.10  #Tautology    : 8
% 1.60/1.10  #SimpNegUnit  : 1
% 1.60/1.10  #BackRed      : 0
% 1.60/1.10  
% 1.60/1.10  #Partial instantiations: 0
% 1.60/1.10  #Strategies tried      : 1
% 1.60/1.10  
% 1.60/1.10  Timing (in seconds)
% 1.60/1.10  ----------------------
% 1.60/1.10  Preprocessing        : 0.23
% 1.60/1.10  Parsing              : 0.13
% 1.60/1.10  CNF conversion       : 0.01
% 1.60/1.10  Main loop            : 0.08
% 1.60/1.10  Inferencing          : 0.04
% 1.60/1.10  Reduction            : 0.02
% 1.60/1.10  Demodulation         : 0.02
% 1.60/1.10  BG Simplification    : 0.01
% 1.60/1.10  Subsumption          : 0.01
% 1.60/1.10  Abstraction          : 0.00
% 1.60/1.10  MUC search           : 0.00
% 1.60/1.10  Cooper               : 0.00
% 1.60/1.10  Total                : 0.34
% 1.60/1.10  Index Insertion      : 0.00
% 1.60/1.10  Index Deletion       : 0.00
% 1.60/1.10  Index Matching       : 0.00
% 1.60/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
