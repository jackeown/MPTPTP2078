%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  46 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_11] :
      ( k7_relat_1(A_11,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    ! [A_2] : k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_98,plain,(
    ! [C_15,A_16,B_17] :
      ( k7_relat_1(k7_relat_1(C_15,A_16),B_17) = k7_relat_1(C_15,A_16)
      | ~ r1_tarski(A_16,B_17)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [A_2,B_17] :
      ( k7_relat_1(k6_relat_1(A_2),k1_xboole_0) = k7_relat_1(k1_xboole_0,B_17)
      | ~ r1_tarski(k1_xboole_0,B_17)
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_98])).

tff(c_132,plain,(
    ! [B_18] : k7_relat_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_50,c_116])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_140,plain,(
    ! [B_18] :
      ( k9_relat_1(k1_xboole_0,B_18) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_147,plain,(
    ! [B_18] : k9_relat_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_140])).

tff(c_22,plain,(
    k9_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.83/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.19  
% 1.83/1.20  tff(f_52, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.83/1.20  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.83/1.20  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.20  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.83/1.20  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.83/1.20  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.83/1.20  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.83/1.20  tff(f_55, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.83/1.20  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.20  tff(c_32, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.20  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_32])).
% 1.83/1.20  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.20  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.20  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.20  tff(c_39, plain, (![A_11]: (k7_relat_1(A_11, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.20  tff(c_50, plain, (![A_2]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_39])).
% 1.83/1.20  tff(c_98, plain, (![C_15, A_16, B_17]: (k7_relat_1(k7_relat_1(C_15, A_16), B_17)=k7_relat_1(C_15, A_16) | ~r1_tarski(A_16, B_17) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.20  tff(c_116, plain, (![A_2, B_17]: (k7_relat_1(k6_relat_1(A_2), k1_xboole_0)=k7_relat_1(k1_xboole_0, B_17) | ~r1_tarski(k1_xboole_0, B_17) | ~v1_relat_1(k6_relat_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_98])).
% 1.83/1.20  tff(c_132, plain, (![B_18]: (k7_relat_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_50, c_116])).
% 1.83/1.20  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.20  tff(c_140, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_14])).
% 1.83/1.20  tff(c_147, plain, (![B_18]: (k9_relat_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_140])).
% 1.83/1.20  tff(c_22, plain, (k9_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.20  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_22])).
% 1.83/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  Inference rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Ref     : 0
% 1.83/1.20  #Sup     : 36
% 1.83/1.20  #Fact    : 0
% 1.83/1.20  #Define  : 0
% 1.83/1.20  #Split   : 0
% 1.83/1.20  #Chain   : 0
% 1.83/1.20  #Close   : 0
% 1.83/1.20  
% 1.83/1.20  Ordering : KBO
% 1.83/1.20  
% 1.83/1.20  Simplification rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Subsume      : 0
% 1.83/1.20  #Demod        : 24
% 1.83/1.20  #Tautology    : 24
% 1.83/1.20  #SimpNegUnit  : 0
% 1.83/1.20  #BackRed      : 1
% 1.83/1.20  
% 1.83/1.20  #Partial instantiations: 0
% 1.83/1.20  #Strategies tried      : 1
% 1.83/1.20  
% 1.83/1.20  Timing (in seconds)
% 1.83/1.20  ----------------------
% 1.83/1.20  Preprocessing        : 0.26
% 1.83/1.20  Parsing              : 0.15
% 1.83/1.20  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.14
% 1.83/1.21  Inferencing          : 0.06
% 1.83/1.21  Reduction            : 0.04
% 1.83/1.21  Demodulation         : 0.03
% 1.83/1.21  BG Simplification    : 0.01
% 1.83/1.21  Subsumption          : 0.02
% 1.83/1.21  Abstraction          : 0.01
% 1.83/1.21  MUC search           : 0.00
% 1.83/1.21  Cooper               : 0.00
% 1.83/1.21  Total                : 0.42
% 1.83/1.21  Index Insertion      : 0.00
% 1.83/1.21  Index Deletion       : 0.00
% 1.83/1.21  Index Matching       : 0.00
% 1.83/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
