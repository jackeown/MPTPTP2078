%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  50 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_30])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [A_9] :
      ( k7_relat_1(A_9,k1_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_46,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_51,plain,(
    ! [C_10,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_10,A_11),B_12) = k7_relat_1(C_10,A_11)
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [B_12] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_12)
      | ~ r1_tarski(k1_xboole_0,B_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_82,plain,(
    ! [B_12] : k7_relat_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_46,c_70])).

tff(c_16,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.71/1.16  
% 1.71/1.16  %Foreground sorts:
% 1.71/1.16  
% 1.71/1.16  
% 1.71/1.16  %Background operators:
% 1.71/1.16  
% 1.71/1.16  
% 1.71/1.16  %Foreground operators:
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.16  
% 1.71/1.17  tff(f_39, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.71/1.17  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.71/1.17  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.71/1.17  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.17  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.71/1.17  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.71/1.17  tff(f_46, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.71/1.17  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.17  tff(c_30, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.17  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_30])).
% 1.71/1.17  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.17  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.17  tff(c_33, plain, (![A_9]: (k7_relat_1(A_9, k1_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.71/1.17  tff(c_42, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_33])).
% 1.71/1.17  tff(c_46, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 1.71/1.18  tff(c_51, plain, (![C_10, A_11, B_12]: (k7_relat_1(k7_relat_1(C_10, A_11), B_12)=k7_relat_1(C_10, A_11) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.18  tff(c_70, plain, (![B_12]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_12) | ~r1_tarski(k1_xboole_0, B_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 1.71/1.18  tff(c_82, plain, (![B_12]: (k7_relat_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_46, c_70])).
% 1.71/1.18  tff(c_16, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.18  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 1.71/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  Inference rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Ref     : 0
% 1.71/1.18  #Sup     : 20
% 1.71/1.18  #Fact    : 0
% 1.71/1.18  #Define  : 0
% 1.71/1.18  #Split   : 0
% 1.71/1.18  #Chain   : 0
% 1.71/1.18  #Close   : 0
% 1.71/1.18  
% 1.71/1.18  Ordering : KBO
% 1.71/1.18  
% 1.71/1.18  Simplification rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Subsume      : 0
% 1.71/1.18  #Demod        : 6
% 1.71/1.18  #Tautology    : 15
% 1.71/1.18  #SimpNegUnit  : 0
% 1.71/1.18  #BackRed      : 1
% 1.71/1.18  
% 1.71/1.18  #Partial instantiations: 0
% 1.71/1.18  #Strategies tried      : 1
% 1.71/1.18  
% 1.71/1.18  Timing (in seconds)
% 1.71/1.18  ----------------------
% 1.71/1.18  Preprocessing        : 0.24
% 1.71/1.18  Parsing              : 0.14
% 1.71/1.18  CNF conversion       : 0.01
% 1.71/1.18  Main loop            : 0.15
% 1.71/1.18  Inferencing          : 0.06
% 1.71/1.18  Reduction            : 0.06
% 1.71/1.18  Demodulation         : 0.05
% 1.71/1.18  BG Simplification    : 0.01
% 1.71/1.18  Subsumption          : 0.02
% 1.71/1.18  Abstraction          : 0.01
% 1.71/1.18  MUC search           : 0.00
% 1.71/1.18  Cooper               : 0.00
% 1.71/1.18  Total                : 0.44
% 1.71/1.18  Index Insertion      : 0.00
% 1.71/1.18  Index Deletion       : 0.00
% 1.71/1.18  Index Matching       : 0.00
% 1.71/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
