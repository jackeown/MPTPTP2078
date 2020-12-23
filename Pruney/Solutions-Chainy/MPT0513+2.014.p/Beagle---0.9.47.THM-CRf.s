%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:00 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [B_9,A_10] :
      ( r1_xboole_0(B_9,A_10)
      | ~ r1_xboole_0(A_10,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [B_12,A_13] :
      ( k7_relat_1(B_12,A_13) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_12),A_13)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_52,plain,(
    ! [A_13] : k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_49])).

tff(c_18,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.09  
% 1.70/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.09  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.70/1.09  
% 1.70/1.09  %Foreground sorts:
% 1.70/1.09  
% 1.70/1.09  
% 1.70/1.09  %Background operators:
% 1.70/1.09  
% 1.70/1.09  
% 1.70/1.09  %Foreground operators:
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.70/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.09  
% 1.70/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.10  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.70/1.10  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.70/1.10  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.70/1.10  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.70/1.10  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.70/1.10  tff(f_48, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.70/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.10  tff(c_28, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.10  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_28])).
% 1.70/1.10  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.70/1.10  tff(c_33, plain, (![B_9, A_10]: (r1_xboole_0(B_9, A_10) | ~r1_xboole_0(A_10, B_9))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.70/1.10  tff(c_36, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.70/1.10  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.10  tff(c_42, plain, (![B_12, A_13]: (k7_relat_1(B_12, A_13)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_12), A_13) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.10  tff(c_49, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_13) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_42])).
% 1.70/1.10  tff(c_52, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_49])).
% 1.70/1.10  tff(c_18, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.10  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 1.70/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  Inference rules
% 1.70/1.10  ----------------------
% 1.70/1.10  #Ref     : 0
% 1.70/1.10  #Sup     : 9
% 1.70/1.10  #Fact    : 0
% 1.70/1.10  #Define  : 0
% 1.70/1.10  #Split   : 0
% 1.70/1.10  #Chain   : 0
% 1.70/1.10  #Close   : 0
% 1.70/1.10  
% 1.70/1.10  Ordering : KBO
% 1.70/1.10  
% 1.70/1.10  Simplification rules
% 1.70/1.10  ----------------------
% 1.70/1.10  #Subsume      : 0
% 1.70/1.10  #Demod        : 4
% 1.70/1.10  #Tautology    : 5
% 1.70/1.10  #SimpNegUnit  : 0
% 1.70/1.10  #BackRed      : 1
% 1.70/1.10  
% 1.70/1.10  #Partial instantiations: 0
% 1.70/1.10  #Strategies tried      : 1
% 1.70/1.10  
% 1.70/1.10  Timing (in seconds)
% 1.70/1.10  ----------------------
% 1.70/1.10  Preprocessing        : 0.25
% 1.70/1.10  Parsing              : 0.14
% 1.70/1.10  CNF conversion       : 0.01
% 1.70/1.10  Main loop            : 0.09
% 1.70/1.10  Inferencing          : 0.04
% 1.70/1.10  Reduction            : 0.02
% 1.70/1.10  Demodulation         : 0.02
% 1.70/1.10  BG Simplification    : 0.01
% 1.70/1.10  Subsumption          : 0.01
% 1.70/1.10  Abstraction          : 0.00
% 1.70/1.10  MUC search           : 0.00
% 1.70/1.10  Cooper               : 0.00
% 1.70/1.10  Total                : 0.36
% 1.70/1.10  Index Insertion      : 0.00
% 1.70/1.10  Index Deletion       : 0.00
% 1.70/1.10  Index Matching       : 0.00
% 1.70/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
