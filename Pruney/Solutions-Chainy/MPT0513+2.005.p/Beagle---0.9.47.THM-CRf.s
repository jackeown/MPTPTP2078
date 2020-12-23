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
% DateTime   : Thu Dec  3 09:59:59 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k7_relat_1(B_6,A_5),B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_12,A_13] :
      ( B_12 = A_13
      | ~ r1_tarski(B_12,A_13)
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

tff(c_43,plain,(
    ! [A_5] :
      ( k7_relat_1(k1_xboole_0,A_5) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_54,plain,(
    ! [A_5] : k7_relat_1(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_43])).

tff(c_16,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.31  
% 1.69/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.31  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.69/1.31  
% 1.69/1.31  %Foreground sorts:
% 1.69/1.31  
% 1.69/1.31  
% 1.69/1.31  %Background operators:
% 1.69/1.31  
% 1.69/1.31  
% 1.69/1.31  %Foreground operators:
% 1.69/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.31  
% 1.82/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.82/1.32  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.82/1.32  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.82/1.32  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.82/1.32  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.32  tff(f_45, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.82/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.82/1.32  tff(c_20, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.32  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_20])).
% 1.82/1.32  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k7_relat_1(B_6, A_5), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.32  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.82/1.32  tff(c_26, plain, (![B_12, A_13]: (B_12=A_13 | ~r1_tarski(B_12, A_13) | ~r1_tarski(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.32  tff(c_39, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_26])).
% 1.82/1.32  tff(c_43, plain, (![A_5]: (k7_relat_1(k1_xboole_0, A_5)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_39])).
% 1.82/1.32  tff(c_54, plain, (![A_5]: (k7_relat_1(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_43])).
% 1.82/1.32  tff(c_16, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.32  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 1.82/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.32  
% 1.82/1.32  Inference rules
% 1.82/1.32  ----------------------
% 1.82/1.32  #Ref     : 0
% 1.82/1.32  #Sup     : 8
% 1.82/1.32  #Fact    : 0
% 1.82/1.32  #Define  : 0
% 1.82/1.32  #Split   : 0
% 1.82/1.32  #Chain   : 0
% 1.82/1.32  #Close   : 0
% 1.82/1.32  
% 1.82/1.32  Ordering : KBO
% 1.82/1.32  
% 1.82/1.32  Simplification rules
% 1.82/1.32  ----------------------
% 1.82/1.32  #Subsume      : 0
% 1.82/1.32  #Demod        : 5
% 1.82/1.32  #Tautology    : 4
% 1.82/1.32  #SimpNegUnit  : 0
% 1.82/1.32  #BackRed      : 1
% 1.82/1.32  
% 1.82/1.32  #Partial instantiations: 0
% 1.82/1.32  #Strategies tried      : 1
% 1.82/1.32  
% 1.82/1.32  Timing (in seconds)
% 1.82/1.32  ----------------------
% 1.82/1.32  Preprocessing        : 0.33
% 1.82/1.32  Parsing              : 0.20
% 1.82/1.32  CNF conversion       : 0.01
% 1.82/1.32  Main loop            : 0.09
% 1.82/1.32  Inferencing          : 0.04
% 1.82/1.32  Reduction            : 0.02
% 1.82/1.32  Demodulation         : 0.02
% 1.82/1.32  BG Simplification    : 0.01
% 1.82/1.32  Subsumption          : 0.01
% 1.82/1.32  Abstraction          : 0.00
% 1.82/1.32  MUC search           : 0.00
% 1.82/1.32  Cooper               : 0.00
% 1.82/1.32  Total                : 0.44
% 1.82/1.32  Index Insertion      : 0.00
% 1.82/1.32  Index Deletion       : 0.00
% 1.82/1.32  Index Matching       : 0.00
% 1.82/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
