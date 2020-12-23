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
% DateTime   : Thu Dec  3 10:02:28 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(k1_relat_1(C),A)
         => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_32,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_11] :
      ( k7_relat_1(A_11,k1_relat_1(A_11)) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [C_18,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_18,A_19),B_20) = k7_relat_1(C_18,A_19)
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_24,B_25] :
      ( k7_relat_1(A_24,k1_relat_1(A_24)) = k7_relat_1(A_24,B_25)
      | ~ r1_tarski(k1_relat_1(A_24),B_25)
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_107,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_110,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_123,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_136,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_123])).

tff(c_6,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_10,A_8,B_9] :
      ( k6_subset_1(k7_relat_1(C_10,A_8),k7_relat_1(C_10,B_9)) = k7_relat_1(C_10,k6_subset_1(A_8,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [C_10,A_8,B_9] :
      ( k4_xboole_0(k7_relat_1(C_10,A_8),k7_relat_1(C_10,B_9)) = k7_relat_1(C_10,k4_xboole_0(A_8,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_10])).

tff(c_144,plain,(
    ! [B_9] :
      ( k7_relat_1('#skF_3',k4_xboole_0('#skF_1',B_9)) = k4_xboole_0('#skF_3',k7_relat_1('#skF_3',B_9))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_20])).

tff(c_154,plain,(
    ! [B_9] : k7_relat_1('#skF_3',k4_xboole_0('#skF_1',B_9)) = k4_xboole_0('#skF_3',k7_relat_1('#skF_3',B_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_144])).

tff(c_14,plain,(
    k7_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2')) != k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_19,plain,(
    k7_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_14])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 1.88/1.20  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.88/1.20  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.88/1.20  tff(f_32, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.88/1.20  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 1.88/1.20  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.20  tff(c_16, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.20  tff(c_12, plain, (![A_11]: (k7_relat_1(A_11, k1_relat_1(A_11))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.20  tff(c_56, plain, (![C_18, A_19, B_20]: (k7_relat_1(k7_relat_1(C_18, A_19), B_20)=k7_relat_1(C_18, A_19) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.20  tff(c_105, plain, (![A_24, B_25]: (k7_relat_1(A_24, k1_relat_1(A_24))=k7_relat_1(A_24, B_25) | ~r1_tarski(k1_relat_1(A_24), B_25) | ~v1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56])).
% 1.88/1.20  tff(c_107, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_105])).
% 1.88/1.20  tff(c_110, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_107])).
% 1.88/1.20  tff(c_123, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 1.88/1.20  tff(c_136, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_123])).
% 1.88/1.20  tff(c_6, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.20  tff(c_10, plain, (![C_10, A_8, B_9]: (k6_subset_1(k7_relat_1(C_10, A_8), k7_relat_1(C_10, B_9))=k7_relat_1(C_10, k6_subset_1(A_8, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.20  tff(c_20, plain, (![C_10, A_8, B_9]: (k4_xboole_0(k7_relat_1(C_10, A_8), k7_relat_1(C_10, B_9))=k7_relat_1(C_10, k4_xboole_0(A_8, B_9)) | ~v1_relat_1(C_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_10])).
% 1.88/1.20  tff(c_144, plain, (![B_9]: (k7_relat_1('#skF_3', k4_xboole_0('#skF_1', B_9))=k4_xboole_0('#skF_3', k7_relat_1('#skF_3', B_9)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_20])).
% 1.88/1.20  tff(c_154, plain, (![B_9]: (k7_relat_1('#skF_3', k4_xboole_0('#skF_1', B_9))=k4_xboole_0('#skF_3', k7_relat_1('#skF_3', B_9)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_144])).
% 1.88/1.20  tff(c_14, plain, (k7_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2'))!=k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.20  tff(c_19, plain, (k7_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_14])).
% 1.88/1.20  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_19])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 55
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 0
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 0
% 1.88/1.20  #Demod        : 37
% 1.88/1.20  #Tautology    : 29
% 1.88/1.20  #SimpNegUnit  : 0
% 1.88/1.20  #BackRed      : 2
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.20  Preprocessing        : 0.28
% 1.88/1.20  Parsing              : 0.15
% 1.88/1.20  CNF conversion       : 0.02
% 1.88/1.20  Main loop            : 0.17
% 1.88/1.20  Inferencing          : 0.07
% 1.95/1.20  Reduction            : 0.05
% 1.95/1.20  Demodulation         : 0.04
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.02
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.48
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
