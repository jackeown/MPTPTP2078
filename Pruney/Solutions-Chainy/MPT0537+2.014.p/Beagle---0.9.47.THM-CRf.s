%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:21 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
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
%$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_10,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_23,plain,(
    ! [B_8,A_9] :
      ( v1_xboole_0(k8_relat_1(B_8,A_9))
      | ~ v1_xboole_0(B_8)
      | ~ v1_relat_1(A_9) ) ),
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
    ! [B_12,A_13] :
      ( k8_relat_1(B_12,A_13) = k1_xboole_0
      | ~ v1_xboole_0(B_12)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_23,c_16])).

tff(c_39,plain,(
    ! [A_14] :
      ( k8_relat_1(k1_xboole_0,A_14) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_45,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.59/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  %$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.59/1.16  
% 1.59/1.16  %Foreground sorts:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Background operators:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Foreground operators:
% 1.59/1.16  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.16  
% 1.59/1.16  tff(f_47, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.59/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.59/1.16  tff(f_42, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 1.59/1.16  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.59/1.16  tff(c_10, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.59/1.16  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.59/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.59/1.16  tff(c_23, plain, (![B_8, A_9]: (v1_xboole_0(k8_relat_1(B_8, A_9)) | ~v1_xboole_0(B_8) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.16  tff(c_13, plain, (![B_5, A_6]: (~v1_xboole_0(B_5) | B_5=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.16  tff(c_16, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2, c_13])).
% 1.59/1.16  tff(c_32, plain, (![B_12, A_13]: (k8_relat_1(B_12, A_13)=k1_xboole_0 | ~v1_xboole_0(B_12) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_23, c_16])).
% 1.59/1.16  tff(c_39, plain, (![A_14]: (k8_relat_1(k1_xboole_0, A_14)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.59/1.16  tff(c_45, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.59/1.16  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_45])).
% 1.59/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  Inference rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Ref     : 0
% 1.59/1.16  #Sup     : 8
% 1.59/1.16  #Fact    : 0
% 1.59/1.16  #Define  : 0
% 1.59/1.16  #Split   : 0
% 1.59/1.16  #Chain   : 0
% 1.59/1.16  #Close   : 0
% 1.59/1.16  
% 1.59/1.16  Ordering : KBO
% 1.59/1.16  
% 1.59/1.16  Simplification rules
% 1.59/1.16  ----------------------
% 1.59/1.16  #Subsume      : 0
% 1.59/1.16  #Demod        : 0
% 1.59/1.16  #Tautology    : 1
% 1.59/1.16  #SimpNegUnit  : 1
% 1.59/1.16  #BackRed      : 0
% 1.59/1.16  
% 1.59/1.16  #Partial instantiations: 0
% 1.59/1.16  #Strategies tried      : 1
% 1.59/1.16  
% 1.59/1.16  Timing (in seconds)
% 1.59/1.16  ----------------------
% 1.59/1.17  Preprocessing        : 0.27
% 1.59/1.17  Parsing              : 0.15
% 1.59/1.17  CNF conversion       : 0.02
% 1.59/1.17  Main loop            : 0.10
% 1.59/1.17  Inferencing          : 0.04
% 1.59/1.17  Reduction            : 0.02
% 1.59/1.17  Demodulation         : 0.01
% 1.59/1.17  BG Simplification    : 0.01
% 1.59/1.17  Subsumption          : 0.02
% 1.59/1.17  Abstraction          : 0.00
% 1.59/1.17  MUC search           : 0.00
% 1.59/1.17  Cooper               : 0.00
% 1.59/1.17  Total                : 0.38
% 1.59/1.17  Index Insertion      : 0.00
% 1.59/1.17  Index Deletion       : 0.00
% 1.59/1.17  Index Matching       : 0.00
% 1.59/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
