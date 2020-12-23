%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:01 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_39,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_42,plain,(
    ! [A_1] : r1_xboole_0(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_39])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [B_14,A_15] :
      ( k7_relat_1(B_14,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_14),A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [A_15] :
      ( k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_59,plain,(
    ! [A_15] : k7_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_56])).

tff(c_18,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:16:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  
% 1.57/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.57/1.07  
% 1.57/1.07  %Foreground sorts:
% 1.57/1.07  
% 1.57/1.07  
% 1.57/1.07  %Background operators:
% 1.57/1.07  
% 1.57/1.07  
% 1.57/1.07  %Foreground operators:
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.57/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.57/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.57/1.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.57/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.57/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.08  
% 1.64/1.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.64/1.08  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.64/1.08  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.64/1.08  tff(f_30, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.64/1.08  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.64/1.08  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.64/1.08  tff(f_46, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.64/1.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.64/1.08  tff(c_34, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.64/1.08  tff(c_38, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.64/1.08  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.64/1.08  tff(c_39, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.64/1.08  tff(c_42, plain, (![A_1]: (r1_xboole_0(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_39])).
% 1.64/1.08  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.08  tff(c_50, plain, (![B_14, A_15]: (k7_relat_1(B_14, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_14), A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.08  tff(c_56, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_15) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_50])).
% 1.64/1.08  tff(c_59, plain, (![A_15]: (k7_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_56])).
% 1.64/1.08  tff(c_18, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.08  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_18])).
% 1.64/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  Inference rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Ref     : 0
% 1.64/1.08  #Sup     : 11
% 1.64/1.08  #Fact    : 0
% 1.64/1.08  #Define  : 0
% 1.64/1.08  #Split   : 0
% 1.64/1.08  #Chain   : 0
% 1.64/1.08  #Close   : 0
% 1.64/1.08  
% 1.64/1.08  Ordering : KBO
% 1.64/1.08  
% 1.64/1.08  Simplification rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Subsume      : 0
% 1.64/1.08  #Demod        : 5
% 1.64/1.08  #Tautology    : 8
% 1.64/1.08  #SimpNegUnit  : 0
% 1.64/1.08  #BackRed      : 1
% 1.64/1.08  
% 1.64/1.08  #Partial instantiations: 0
% 1.64/1.08  #Strategies tried      : 1
% 1.64/1.08  
% 1.64/1.08  Timing (in seconds)
% 1.64/1.08  ----------------------
% 1.64/1.09  Preprocessing        : 0.25
% 1.64/1.09  Parsing              : 0.14
% 1.64/1.09  CNF conversion       : 0.01
% 1.64/1.09  Main loop            : 0.09
% 1.64/1.09  Inferencing          : 0.04
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.02
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.01
% 1.64/1.09  Abstraction          : 0.00
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.09  Cooper               : 0.00
% 1.64/1.09  Total                : 0.36
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
