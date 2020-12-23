%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:01 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [B_7,A_8] :
      ( k7_relat_1(B_7,A_8) = B_7
      | ~ r1_tarski(k1_relat_1(B_7),A_8)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_8] :
      ( k7_relat_1(k1_xboole_0,A_8) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_29])).

tff(c_34,plain,(
    ! [A_8] : k7_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_32])).

tff(c_14,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.48/1.06  
% 1.48/1.06  %Foreground sorts:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Background operators:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Foreground operators:
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.48/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.48/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.48/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.48/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.48/1.06  
% 1.60/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.07  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.60/1.07  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.60/1.07  tff(f_35, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.60/1.07  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.60/1.07  tff(f_44, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.60/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.07  tff(c_24, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.07  tff(c_28, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_24])).
% 1.60/1.07  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.60/1.07  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.07  tff(c_29, plain, (![B_7, A_8]: (k7_relat_1(B_7, A_8)=B_7 | ~r1_tarski(k1_relat_1(B_7), A_8) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.07  tff(c_32, plain, (![A_8]: (k7_relat_1(k1_xboole_0, A_8)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_8) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_29])).
% 1.60/1.07  tff(c_34, plain, (![A_8]: (k7_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_32])).
% 1.60/1.07  tff(c_14, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.07  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 1.60/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  Inference rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Ref     : 0
% 1.60/1.07  #Sup     : 6
% 1.60/1.07  #Fact    : 0
% 1.60/1.07  #Define  : 0
% 1.60/1.07  #Split   : 0
% 1.60/1.07  #Chain   : 0
% 1.60/1.07  #Close   : 0
% 1.60/1.07  
% 1.60/1.07  Ordering : KBO
% 1.60/1.07  
% 1.60/1.07  Simplification rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Subsume      : 0
% 1.60/1.07  #Demod        : 3
% 1.60/1.07  #Tautology    : 4
% 1.60/1.07  #SimpNegUnit  : 0
% 1.60/1.07  #BackRed      : 1
% 1.60/1.07  
% 1.60/1.07  #Partial instantiations: 0
% 1.60/1.07  #Strategies tried      : 1
% 1.60/1.07  
% 1.60/1.07  Timing (in seconds)
% 1.60/1.07  ----------------------
% 1.60/1.08  Preprocessing        : 0.24
% 1.60/1.08  Parsing              : 0.14
% 1.60/1.08  CNF conversion       : 0.01
% 1.60/1.08  Main loop            : 0.07
% 1.60/1.08  Inferencing          : 0.04
% 1.60/1.08  Reduction            : 0.02
% 1.60/1.08  Demodulation         : 0.02
% 1.60/1.08  BG Simplification    : 0.01
% 1.60/1.08  Subsumption          : 0.01
% 1.60/1.08  Abstraction          : 0.00
% 1.60/1.08  MUC search           : 0.00
% 1.60/1.08  Cooper               : 0.00
% 1.60/1.08  Total                : 0.34
% 1.60/1.08  Index Insertion      : 0.00
% 1.60/1.08  Index Deletion       : 0.00
% 1.60/1.08  Index Matching       : 0.00
% 1.60/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
