%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:21 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  39 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(B) )
     => ( v1_xboole_0(k5_relat_1(B,A))
        & v1_relat_1(k5_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(c_14,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [B_9,A_10] :
      ( v1_xboole_0(k5_relat_1(B_9,A_10))
      | ~ v1_relat_1(B_9)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_33,plain,(
    ! [B_11,A_12] :
      ( k5_relat_1(B_11,A_12) = k1_xboole_0
      | ~ v1_relat_1(B_11)
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_40,plain,(
    ! [A_13] :
      ( k5_relat_1('#skF_1',A_13) = k1_xboole_0
      | ~ v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_33])).

tff(c_48,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    ! [B_15,A_16] :
      ( k5_relat_1(B_15,k6_relat_1(A_16)) = k8_relat_1(A_16,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,(
    ! [B_17] :
      ( k8_relat_1(k1_xboole_0,B_17) = k5_relat_1(B_17,k1_xboole_0)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_116,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k5_relat_1('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_121,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_116])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.15  
% 1.54/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.15  %$ v1_xboole_0 > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.54/1.15  
% 1.54/1.15  %Foreground sorts:
% 1.54/1.15  
% 1.54/1.15  
% 1.54/1.15  %Background operators:
% 1.54/1.15  
% 1.54/1.15  
% 1.54/1.15  %Foreground operators:
% 1.54/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.54/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.54/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.54/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.54/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.54/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.54/1.15  
% 1.54/1.16  tff(f_48, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 1.54/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.54/1.16  tff(f_38, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(B)) => (v1_xboole_0(k5_relat_1(B, A)) & v1_relat_1(k5_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_relat_1)).
% 1.54/1.16  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.54/1.16  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.54/1.16  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.54/1.16  tff(c_14, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.54/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.54/1.16  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.54/1.16  tff(c_28, plain, (![B_9, A_10]: (v1_xboole_0(k5_relat_1(B_9, A_10)) | ~v1_relat_1(B_9) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.54/1.16  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.54/1.16  tff(c_33, plain, (![B_11, A_12]: (k5_relat_1(B_11, A_12)=k1_xboole_0 | ~v1_relat_1(B_11) | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_28, c_4])).
% 1.54/1.16  tff(c_40, plain, (![A_13]: (k5_relat_1('#skF_1', A_13)=k1_xboole_0 | ~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_16, c_33])).
% 1.54/1.16  tff(c_48, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.54/1.16  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.54/1.16  tff(c_89, plain, (![B_15, A_16]: (k5_relat_1(B_15, k6_relat_1(A_16))=k8_relat_1(A_16, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.54/1.16  tff(c_107, plain, (![B_17]: (k8_relat_1(k1_xboole_0, B_17)=k5_relat_1(B_17, k1_xboole_0) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 1.54/1.16  tff(c_116, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k5_relat_1('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_107])).
% 1.54/1.16  tff(c_121, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_116])).
% 1.54/1.16  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_121])).
% 1.54/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.16  
% 1.54/1.16  Inference rules
% 1.54/1.16  ----------------------
% 1.54/1.16  #Ref     : 0
% 1.54/1.16  #Sup     : 27
% 1.54/1.16  #Fact    : 0
% 1.54/1.16  #Define  : 0
% 1.54/1.16  #Split   : 0
% 1.54/1.16  #Chain   : 0
% 1.54/1.16  #Close   : 0
% 1.54/1.16  
% 1.54/1.16  Ordering : KBO
% 1.54/1.16  
% 1.54/1.16  Simplification rules
% 1.54/1.16  ----------------------
% 1.54/1.16  #Subsume      : 0
% 1.54/1.16  #Demod        : 13
% 1.54/1.16  #Tautology    : 12
% 1.54/1.16  #SimpNegUnit  : 1
% 1.54/1.16  #BackRed      : 0
% 1.54/1.16  
% 1.54/1.16  #Partial instantiations: 0
% 1.54/1.16  #Strategies tried      : 1
% 1.54/1.16  
% 1.54/1.16  Timing (in seconds)
% 1.54/1.16  ----------------------
% 1.54/1.17  Preprocessing        : 0.23
% 1.54/1.17  Parsing              : 0.13
% 1.54/1.17  CNF conversion       : 0.01
% 1.54/1.17  Main loop            : 0.12
% 1.54/1.17  Inferencing          : 0.05
% 1.54/1.17  Reduction            : 0.03
% 1.54/1.17  Demodulation         : 0.02
% 1.54/1.17  BG Simplification    : 0.01
% 1.54/1.17  Subsumption          : 0.02
% 1.54/1.17  Abstraction          : 0.01
% 1.54/1.17  MUC search           : 0.00
% 1.54/1.17  Cooper               : 0.00
% 1.54/1.17  Total                : 0.37
% 1.54/1.17  Index Insertion      : 0.00
% 1.54/1.17  Index Deletion       : 0.00
% 1.54/1.17  Index Matching       : 0.00
% 1.54/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
