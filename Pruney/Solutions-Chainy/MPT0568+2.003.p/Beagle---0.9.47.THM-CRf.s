%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  45 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k10_relat_1(B_24,A_25),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_25] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_25),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_56])).

tff(c_61,plain,(
    ! [A_25] : r1_tarski(k10_relat_1(k1_xboole_0,A_25),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_59])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_2'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( ~ v1_xboole_0(A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_63,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_82,plain,(
    ! [A_25] :
      ( k10_relat_1(k1_xboole_0,A_25) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_61,c_79])).

tff(c_94,plain,(
    ! [A_25] : k10_relat_1(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.81/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.18  
% 1.81/1.19  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.81/1.19  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.81/1.19  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.81/1.19  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.81/1.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.81/1.19  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/1.19  tff(f_59, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.81/1.19  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.19  tff(c_39, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.19  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.81/1.19  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.81/1.19  tff(c_56, plain, (![B_24, A_25]: (r1_tarski(k10_relat_1(B_24, A_25), k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.19  tff(c_59, plain, (![A_25]: (r1_tarski(k10_relat_1(k1_xboole_0, A_25), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_56])).
% 1.81/1.19  tff(c_61, plain, (![A_25]: (r1_tarski(k10_relat_1(k1_xboole_0, A_25), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_59])).
% 1.81/1.19  tff(c_50, plain, (![A_20, B_21]: (r2_hidden('#skF_2'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.19  tff(c_54, plain, (![A_20, B_21]: (~v1_xboole_0(A_20) | r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_50, c_2])).
% 1.81/1.19  tff(c_63, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.19  tff(c_79, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_54, c_63])).
% 1.81/1.19  tff(c_82, plain, (![A_25]: (k10_relat_1(k1_xboole_0, A_25)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_61, c_79])).
% 1.81/1.19  tff(c_94, plain, (![A_25]: (k10_relat_1(k1_xboole_0, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82])).
% 1.81/1.19  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.19  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_28])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 17
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 8
% 1.81/1.19  #Tautology    : 10
% 1.81/1.19  #SimpNegUnit  : 0
% 1.81/1.19  #BackRed      : 2
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.20  Preprocessing        : 0.28
% 1.81/1.20  Parsing              : 0.16
% 1.81/1.20  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.12
% 1.81/1.20  Inferencing          : 0.05
% 1.81/1.20  Reduction            : 0.03
% 1.81/1.20  Demodulation         : 0.03
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.02
% 1.81/1.20  Abstraction          : 0.01
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.43
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
