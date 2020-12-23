%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_32,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_29,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    ! [A_11,B_12] :
      ( k7_relat_1(A_11,B_12) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_29,c_4])).

tff(c_38,plain,(
    ! [B_12] :
      ( k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_42,plain,(
    ! [B_12] : k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_14,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:55:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.07  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.07  
% 1.60/1.07  %Foreground sorts:
% 1.60/1.07  
% 1.60/1.07  
% 1.60/1.07  %Background operators:
% 1.60/1.07  
% 1.60/1.07  
% 1.60/1.07  %Foreground operators:
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.60/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.60/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.07  
% 1.65/1.08  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.65/1.08  tff(f_32, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.65/1.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.65/1.08  tff(f_40, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.65/1.08  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.65/1.08  tff(f_44, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.65/1.08  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.08  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.08  tff(c_18, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_6])).
% 1.65/1.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.65/1.08  tff(c_29, plain, (![A_9, B_10]: (v1_xboole_0(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.08  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.65/1.08  tff(c_34, plain, (![A_11, B_12]: (k7_relat_1(A_11, B_12)=k1_xboole_0 | ~v1_relat_1(A_11) | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_29, c_4])).
% 1.65/1.08  tff(c_38, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.65/1.08  tff(c_42, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 1.65/1.08  tff(c_14, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.08  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 1.65/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.08  
% 1.65/1.08  Inference rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Ref     : 0
% 1.65/1.08  #Sup     : 8
% 1.65/1.08  #Fact    : 0
% 1.65/1.08  #Define  : 0
% 1.65/1.08  #Split   : 0
% 1.65/1.08  #Chain   : 0
% 1.65/1.08  #Close   : 0
% 1.65/1.08  
% 1.65/1.08  Ordering : KBO
% 1.65/1.08  
% 1.65/1.08  Simplification rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Subsume      : 0
% 1.65/1.08  #Demod        : 2
% 1.65/1.08  #Tautology    : 3
% 1.65/1.08  #SimpNegUnit  : 0
% 1.65/1.08  #BackRed      : 1
% 1.65/1.08  
% 1.65/1.08  #Partial instantiations: 0
% 1.65/1.08  #Strategies tried      : 1
% 1.65/1.08  
% 1.65/1.08  Timing (in seconds)
% 1.65/1.08  ----------------------
% 1.65/1.09  Preprocessing        : 0.24
% 1.65/1.09  Parsing              : 0.13
% 1.65/1.09  CNF conversion       : 0.01
% 1.65/1.09  Main loop            : 0.09
% 1.65/1.09  Inferencing          : 0.04
% 1.65/1.09  Reduction            : 0.02
% 1.65/1.09  Demodulation         : 0.02
% 1.65/1.09  BG Simplification    : 0.01
% 1.65/1.09  Subsumption          : 0.02
% 1.65/1.09  Abstraction          : 0.00
% 1.65/1.09  MUC search           : 0.00
% 1.65/1.09  Cooper               : 0.00
% 1.65/1.09  Total                : 0.36
% 1.65/1.09  Index Insertion      : 0.00
% 1.65/1.09  Index Deletion       : 0.00
% 1.65/1.09  Index Matching       : 0.00
% 1.65/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
