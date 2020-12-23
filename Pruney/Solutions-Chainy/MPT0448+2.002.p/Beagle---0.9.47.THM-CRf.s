%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k1_tarski(k4_tarski(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k1_tarski(k4_tarski(A_6,B_7))) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_relat_1(k1_tarski(k4_tarski(A_8,B_9))) = k1_tarski(B_9)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_8,B_9] : k2_relat_1(k1_tarski(k4_tarski(A_8,B_9))) = k1_tarski(B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_8,B_9))) = k1_tarski(A_8)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_8,B_9] : k1_relat_1(k1_tarski(k4_tarski(A_8,B_9))) = k1_tarski(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_52,plain,(
    ! [A_21] :
      ( k2_xboole_0(k1_relat_1(A_21),k2_relat_1(A_21)) = k3_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(k1_tarski(A_8),k2_relat_1(k1_tarski(k4_tarski(A_8,B_9)))) = k3_relat_1(k1_tarski(k4_tarski(A_8,B_9)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_8,B_9))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_68,plain,(
    ! [A_8,B_9] : k3_relat_1(k1_tarski(k4_tarski(A_8,B_9))) = k2_tarski(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_18,c_61])).

tff(c_14,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.13  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.66/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.13  
% 1.66/1.13  tff(f_37, axiom, (![A, B]: v1_relat_1(k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_relat_1)).
% 1.66/1.13  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.66/1.13  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 1.66/1.13  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.66/1.13  tff(f_48, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 1.66/1.13  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k1_tarski(k4_tarski(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.13  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.13  tff(c_10, plain, (![A_8, B_9]: (k2_relat_1(k1_tarski(k4_tarski(A_8, B_9)))=k1_tarski(B_9) | ~v1_relat_1(k1_tarski(k4_tarski(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.13  tff(c_18, plain, (![A_8, B_9]: (k2_relat_1(k1_tarski(k4_tarski(A_8, B_9)))=k1_tarski(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.66/1.13  tff(c_12, plain, (![A_8, B_9]: (k1_relat_1(k1_tarski(k4_tarski(A_8, B_9)))=k1_tarski(A_8) | ~v1_relat_1(k1_tarski(k4_tarski(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.13  tff(c_16, plain, (![A_8, B_9]: (k1_relat_1(k1_tarski(k4_tarski(A_8, B_9)))=k1_tarski(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.66/1.13  tff(c_52, plain, (![A_21]: (k2_xboole_0(k1_relat_1(A_21), k2_relat_1(A_21))=k3_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.13  tff(c_61, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k2_relat_1(k1_tarski(k4_tarski(A_8, B_9))))=k3_relat_1(k1_tarski(k4_tarski(A_8, B_9))) | ~v1_relat_1(k1_tarski(k4_tarski(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_52])).
% 1.66/1.13  tff(c_68, plain, (![A_8, B_9]: (k3_relat_1(k1_tarski(k4_tarski(A_8, B_9)))=k2_tarski(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_18, c_61])).
% 1.66/1.13  tff(c_14, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.13  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_14])).
% 1.66/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  Inference rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Ref     : 1
% 1.66/1.13  #Sup     : 10
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 0
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 9
% 1.66/1.13  #Tautology    : 9
% 1.66/1.13  #SimpNegUnit  : 0
% 1.66/1.13  #BackRed      : 1
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.14  Preprocessing        : 0.26
% 1.66/1.14  Parsing              : 0.15
% 1.66/1.14  CNF conversion       : 0.01
% 1.76/1.14  Main loop            : 0.08
% 1.76/1.14  Inferencing          : 0.03
% 1.76/1.14  Reduction            : 0.03
% 1.76/1.14  Demodulation         : 0.03
% 1.76/1.14  BG Simplification    : 0.01
% 1.76/1.14  Subsumption          : 0.01
% 1.76/1.14  Abstraction          : 0.00
% 1.76/1.14  MUC search           : 0.00
% 1.76/1.14  Cooper               : 0.00
% 1.76/1.14  Total                : 0.37
% 1.76/1.14  Index Insertion      : 0.00
% 1.76/1.14  Index Deletion       : 0.00
% 1.76/1.14  Index Matching       : 0.00
% 1.76/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
