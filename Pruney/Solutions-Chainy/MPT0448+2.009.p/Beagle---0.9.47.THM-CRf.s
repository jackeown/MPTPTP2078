%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  47 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19,D_20] : v1_relat_1(k2_tarski(k4_tarski(A_17,B_18),k4_tarski(C_19,D_20))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_17,B_18] : v1_relat_1(k1_tarski(k4_tarski(A_17,B_18))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] : v1_relat_1(k2_tarski(k4_tarski(A_7,B_8),k4_tarski(C_9,D_10))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_11,B_12),k4_tarski(C_13,D_14))) = k2_tarski(B_12,D_14)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_11,B_12),k4_tarski(C_13,D_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_relat_1(k2_tarski(k4_tarski(A_28,B_29),k4_tarski(C_30,D_31))) = k2_tarski(B_29,D_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_72,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,B_29) = k2_relat_1(k1_tarski(k4_tarski(A_28,B_29))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_77,plain,(
    ! [A_28,B_29] : k2_relat_1(k1_tarski(k4_tarski(A_28,B_29))) = k1_tarski(B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_11,B_12),k4_tarski(C_13,D_14))) = k2_tarski(A_11,C_13)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_11,B_12),k4_tarski(C_13,D_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [A_34,B_35,C_36,D_37] : k1_relat_1(k2_tarski(k4_tarski(A_34,B_35),k4_tarski(C_36,D_37))) = k2_tarski(A_34,C_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_105,plain,(
    ! [A_34,B_35] : k2_tarski(A_34,A_34) = k1_relat_1(k1_tarski(k4_tarski(A_34,B_35))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_111,plain,(
    ! [A_38,B_39] : k1_relat_1(k1_tarski(k4_tarski(A_38,B_39))) = k1_tarski(A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_xboole_0(k1_relat_1(A_6),k2_relat_1(A_6)) = k3_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(k1_tarski(A_38),k2_relat_1(k1_tarski(k4_tarski(A_38,B_39)))) = k3_relat_1(k1_tarski(k4_tarski(A_38,B_39)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_38,B_39))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_123,plain,(
    ! [A_38,B_39] : k3_relat_1(k1_tarski(k4_tarski(A_38,B_39))) = k2_tarski(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2,c_77,c_117])).

tff(c_16,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:58:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  %$ v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.12  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.70/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.12  
% 1.70/1.13  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.70/1.13  tff(f_39, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.70/1.13  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.70/1.13  tff(f_47, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 1.70/1.13  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.70/1.13  tff(f_50, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 1.70/1.13  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.13  tff(c_30, plain, (![A_17, B_18, C_19, D_20]: (v1_relat_1(k2_tarski(k4_tarski(A_17, B_18), k4_tarski(C_19, D_20))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.13  tff(c_34, plain, (![A_17, B_18]: (v1_relat_1(k1_tarski(k4_tarski(A_17, B_18))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_30])).
% 1.70/1.13  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.13  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (v1_relat_1(k2_tarski(k4_tarski(A_7, B_8), k4_tarski(C_9, D_10))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.13  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k2_relat_1(k2_tarski(k4_tarski(A_11, B_12), k4_tarski(C_13, D_14)))=k2_tarski(B_12, D_14) | ~v1_relat_1(k2_tarski(k4_tarski(A_11, B_12), k4_tarski(C_13, D_14))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.13  tff(c_59, plain, (![A_28, B_29, C_30, D_31]: (k2_relat_1(k2_tarski(k4_tarski(A_28, B_29), k4_tarski(C_30, D_31)))=k2_tarski(B_29, D_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.70/1.13  tff(c_72, plain, (![B_29, A_28]: (k2_tarski(B_29, B_29)=k2_relat_1(k1_tarski(k4_tarski(A_28, B_29))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 1.70/1.13  tff(c_77, plain, (![A_28, B_29]: (k2_relat_1(k1_tarski(k4_tarski(A_28, B_29)))=k1_tarski(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_72])).
% 1.70/1.13  tff(c_14, plain, (![A_11, B_12, C_13, D_14]: (k1_relat_1(k2_tarski(k4_tarski(A_11, B_12), k4_tarski(C_13, D_14)))=k2_tarski(A_11, C_13) | ~v1_relat_1(k2_tarski(k4_tarski(A_11, B_12), k4_tarski(C_13, D_14))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.13  tff(c_92, plain, (![A_34, B_35, C_36, D_37]: (k1_relat_1(k2_tarski(k4_tarski(A_34, B_35), k4_tarski(C_36, D_37)))=k2_tarski(A_34, C_36))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 1.70/1.13  tff(c_105, plain, (![A_34, B_35]: (k2_tarski(A_34, A_34)=k1_relat_1(k1_tarski(k4_tarski(A_34, B_35))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 1.70/1.13  tff(c_111, plain, (![A_38, B_39]: (k1_relat_1(k1_tarski(k4_tarski(A_38, B_39)))=k1_tarski(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 1.70/1.13  tff(c_8, plain, (![A_6]: (k2_xboole_0(k1_relat_1(A_6), k2_relat_1(A_6))=k3_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.13  tff(c_117, plain, (![A_38, B_39]: (k2_xboole_0(k1_tarski(A_38), k2_relat_1(k1_tarski(k4_tarski(A_38, B_39))))=k3_relat_1(k1_tarski(k4_tarski(A_38, B_39))) | ~v1_relat_1(k1_tarski(k4_tarski(A_38, B_39))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_8])).
% 1.70/1.13  tff(c_123, plain, (![A_38, B_39]: (k3_relat_1(k1_tarski(k4_tarski(A_38, B_39)))=k2_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2, c_77, c_117])).
% 1.70/1.13  tff(c_16, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.70/1.13  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_16])).
% 1.70/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.13  
% 1.70/1.13  Inference rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Ref     : 1
% 1.70/1.13  #Sup     : 21
% 1.70/1.13  #Fact    : 0
% 1.70/1.13  #Define  : 0
% 1.70/1.13  #Split   : 0
% 1.70/1.13  #Chain   : 0
% 1.70/1.13  #Close   : 0
% 1.70/1.13  
% 1.70/1.13  Ordering : KBO
% 1.70/1.13  
% 1.70/1.13  Simplification rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Subsume      : 0
% 1.70/1.13  #Demod        : 12
% 1.70/1.13  #Tautology    : 15
% 1.70/1.13  #SimpNegUnit  : 0
% 1.70/1.13  #BackRed      : 1
% 1.70/1.13  
% 1.70/1.13  #Partial instantiations: 0
% 1.70/1.13  #Strategies tried      : 1
% 1.70/1.13  
% 1.70/1.13  Timing (in seconds)
% 1.70/1.13  ----------------------
% 1.70/1.13  Preprocessing        : 0.27
% 1.70/1.13  Parsing              : 0.15
% 1.70/1.13  CNF conversion       : 0.02
% 1.70/1.13  Main loop            : 0.10
% 1.70/1.13  Inferencing          : 0.04
% 1.70/1.13  Reduction            : 0.03
% 1.70/1.13  Demodulation         : 0.03
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.01
% 1.70/1.13  Abstraction          : 0.01
% 1.70/1.13  MUC search           : 0.00
% 1.70/1.13  Cooper               : 0.00
% 1.70/1.13  Total                : 0.40
% 1.70/1.13  Index Insertion      : 0.00
% 1.70/1.13  Index Deletion       : 0.00
% 1.70/1.13  Index Matching       : 0.00
% 1.70/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
