%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  41 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_25,B_26,C_27,D_28] : v1_relat_1(k2_tarski(k4_tarski(A_25,B_26),k4_tarski(C_27,D_28))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_25,B_26] : v1_relat_1(k1_tarski(k4_tarski(A_25,B_26))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k1_tarski(k4_tarski(A_16,B_17))) = k1_tarski(B_17)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_16,B_17] : k2_relat_1(k1_tarski(k4_tarski(A_16,B_17))) = k1_tarski(B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_16])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_16,B_17))) = k1_tarski(A_16)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ! [A_40,B_41] : k1_relat_1(k1_tarski(k4_tarski(A_40,B_41))) = k1_tarski(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).

tff(c_12,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(k1_tarski(A_40),k2_relat_1(k1_tarski(k4_tarski(A_40,B_41)))) = k3_relat_1(k1_tarski(k4_tarski(A_40,B_41)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_40,B_41))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_12])).

tff(c_151,plain,(
    ! [A_40,B_41] : k3_relat_1(k1_tarski(k4_tarski(A_40,B_41))) = k2_tarski(A_40,B_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2,c_122,c_145])).

tff(c_20,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  %$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.60/1.16  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.60/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.60/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.60/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.16  
% 1.60/1.17  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.60/1.17  tff(f_41, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.60/1.17  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.60/1.17  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 1.60/1.17  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.60/1.17  tff(f_52, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 1.60/1.17  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.17  tff(c_68, plain, (![A_25, B_26, C_27, D_28]: (v1_relat_1(k2_tarski(k4_tarski(A_25, B_26), k4_tarski(C_27, D_28))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.17  tff(c_72, plain, (![A_25, B_26]: (v1_relat_1(k1_tarski(k4_tarski(A_25, B_26))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 1.60/1.17  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.17  tff(c_16, plain, (![A_16, B_17]: (k2_relat_1(k1_tarski(k4_tarski(A_16, B_17)))=k1_tarski(B_17) | ~v1_relat_1(k1_tarski(k4_tarski(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.17  tff(c_122, plain, (![A_16, B_17]: (k2_relat_1(k1_tarski(k4_tarski(A_16, B_17)))=k1_tarski(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_16])).
% 1.60/1.17  tff(c_18, plain, (![A_16, B_17]: (k1_relat_1(k1_tarski(k4_tarski(A_16, B_17)))=k1_tarski(A_16) | ~v1_relat_1(k1_tarski(k4_tarski(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.17  tff(c_139, plain, (![A_40, B_41]: (k1_relat_1(k1_tarski(k4_tarski(A_40, B_41)))=k1_tarski(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 1.60/1.17  tff(c_12, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.17  tff(c_145, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), k2_relat_1(k1_tarski(k4_tarski(A_40, B_41))))=k3_relat_1(k1_tarski(k4_tarski(A_40, B_41))) | ~v1_relat_1(k1_tarski(k4_tarski(A_40, B_41))))), inference(superposition, [status(thm), theory('equality')], [c_139, c_12])).
% 1.60/1.17  tff(c_151, plain, (![A_40, B_41]: (k3_relat_1(k1_tarski(k4_tarski(A_40, B_41)))=k2_tarski(A_40, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2, c_122, c_145])).
% 1.60/1.17  tff(c_20, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.60/1.17  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_20])).
% 1.60/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  Inference rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Ref     : 0
% 1.60/1.17  #Sup     : 28
% 1.60/1.17  #Fact    : 0
% 1.60/1.17  #Define  : 0
% 1.60/1.17  #Split   : 0
% 1.60/1.17  #Chain   : 0
% 1.60/1.17  #Close   : 0
% 1.60/1.17  
% 1.60/1.17  Ordering : KBO
% 1.60/1.17  
% 1.60/1.17  Simplification rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Subsume      : 0
% 1.60/1.17  #Demod        : 10
% 1.60/1.17  #Tautology    : 23
% 1.60/1.17  #SimpNegUnit  : 0
% 1.60/1.17  #BackRed      : 1
% 1.60/1.17  
% 1.60/1.17  #Partial instantiations: 0
% 1.60/1.17  #Strategies tried      : 1
% 1.60/1.17  
% 1.60/1.17  Timing (in seconds)
% 1.60/1.17  ----------------------
% 1.60/1.17  Preprocessing        : 0.28
% 1.60/1.17  Parsing              : 0.15
% 1.60/1.17  CNF conversion       : 0.02
% 1.60/1.17  Main loop            : 0.10
% 1.60/1.17  Inferencing          : 0.04
% 1.60/1.17  Reduction            : 0.03
% 1.60/1.17  Demodulation         : 0.03
% 1.60/1.17  BG Simplification    : 0.01
% 1.60/1.17  Subsumption          : 0.01
% 1.60/1.17  Abstraction          : 0.01
% 1.60/1.17  MUC search           : 0.00
% 1.60/1.17  Cooper               : 0.00
% 1.60/1.17  Total                : 0.40
% 1.60/1.17  Index Insertion      : 0.00
% 1.60/1.17  Index Deletion       : 0.00
% 1.60/1.17  Index Matching       : 0.00
% 1.60/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
