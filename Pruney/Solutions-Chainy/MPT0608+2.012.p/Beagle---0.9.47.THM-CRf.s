%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [C_9,A_7,B_8] :
      ( k6_subset_1(k7_relat_1(C_9,A_7),k7_relat_1(C_9,B_8)) = k7_relat_1(C_9,k6_subset_1(A_7,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [C_30,A_31,B_32] :
      ( k4_xboole_0(k7_relat_1(C_30,A_31),k7_relat_1(C_30,B_32)) = k7_relat_1(C_30,k4_xboole_0(A_31,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_936,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(A_67,k4_xboole_0(k1_relat_1(A_67),B_68)) = k4_xboole_0(A_67,k7_relat_1(A_67,B_68))
      | ~ v1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [B_28,A_29] :
      ( k1_relat_1(k7_relat_1(B_28,A_29)) = A_29
      | ~ r1_tarski(A_29,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [B_28,B_4] :
      ( k1_relat_1(k7_relat_1(B_28,k4_xboole_0(k1_relat_1(B_28),B_4))) = k4_xboole_0(k1_relat_1(B_28),B_4)
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_2713,plain,(
    ! [A_107,B_108] :
      ( k1_relat_1(k4_xboole_0(A_107,k7_relat_1(A_107,B_108))) = k4_xboole_0(k1_relat_1(A_107),B_108)
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_134])).

tff(c_16,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_2746,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2713,c_19])).

tff(c_2790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n018.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 17:51:26 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.55  
% 3.61/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.55  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.61/1.55  
% 3.61/1.55  %Foreground sorts:
% 3.61/1.55  
% 3.61/1.55  
% 3.61/1.55  %Background operators:
% 3.61/1.55  
% 3.61/1.55  
% 3.61/1.55  %Foreground operators:
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.61/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.61/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.55  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.61/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.55  
% 3.61/1.56  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 3.61/1.56  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.61/1.56  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.61/1.56  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 3.61/1.56  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.61/1.56  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.61/1.56  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.56  tff(c_14, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.56  tff(c_8, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.56  tff(c_10, plain, (![C_9, A_7, B_8]: (k6_subset_1(k7_relat_1(C_9, A_7), k7_relat_1(C_9, B_8))=k7_relat_1(C_9, k6_subset_1(A_7, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.56  tff(c_135, plain, (![C_30, A_31, B_32]: (k4_xboole_0(k7_relat_1(C_30, A_31), k7_relat_1(C_30, B_32))=k7_relat_1(C_30, k4_xboole_0(A_31, B_32)) | ~v1_relat_1(C_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 3.61/1.56  tff(c_936, plain, (![A_67, B_68]: (k7_relat_1(A_67, k4_xboole_0(k1_relat_1(A_67), B_68))=k4_xboole_0(A_67, k7_relat_1(A_67, B_68)) | ~v1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_14, c_135])).
% 3.61/1.56  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.56  tff(c_124, plain, (![B_28, A_29]: (k1_relat_1(k7_relat_1(B_28, A_29))=A_29 | ~r1_tarski(A_29, k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.61/1.56  tff(c_134, plain, (![B_28, B_4]: (k1_relat_1(k7_relat_1(B_28, k4_xboole_0(k1_relat_1(B_28), B_4)))=k4_xboole_0(k1_relat_1(B_28), B_4) | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_6, c_124])).
% 3.61/1.56  tff(c_2713, plain, (![A_107, B_108]: (k1_relat_1(k4_xboole_0(A_107, k7_relat_1(A_107, B_108)))=k4_xboole_0(k1_relat_1(A_107), B_108) | ~v1_relat_1(A_107) | ~v1_relat_1(A_107) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_936, c_134])).
% 3.61/1.56  tff(c_16, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.56  tff(c_19, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 3.61/1.56  tff(c_2746, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2713, c_19])).
% 3.61/1.56  tff(c_2790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2746])).
% 3.61/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.56  
% 3.61/1.56  Inference rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Ref     : 0
% 3.61/1.56  #Sup     : 824
% 3.61/1.56  #Fact    : 0
% 3.61/1.56  #Define  : 0
% 3.61/1.56  #Split   : 2
% 3.61/1.56  #Chain   : 0
% 3.61/1.56  #Close   : 0
% 3.61/1.56  
% 3.61/1.56  Ordering : KBO
% 3.61/1.56  
% 3.61/1.56  Simplification rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Subsume      : 219
% 3.61/1.56  #Demod        : 732
% 3.61/1.56  #Tautology    : 401
% 3.61/1.56  #SimpNegUnit  : 0
% 3.61/1.56  #BackRed      : 6
% 3.61/1.56  
% 3.61/1.56  #Partial instantiations: 0
% 3.61/1.56  #Strategies tried      : 1
% 3.61/1.56  
% 3.61/1.56  Timing (in seconds)
% 3.61/1.56  ----------------------
% 3.61/1.56  Preprocessing        : 0.32
% 3.61/1.56  Parsing              : 0.16
% 3.61/1.56  CNF conversion       : 0.02
% 3.61/1.56  Main loop            : 0.62
% 3.61/1.56  Inferencing          : 0.22
% 3.61/1.56  Reduction            : 0.23
% 3.61/1.56  Demodulation         : 0.17
% 3.61/1.56  BG Simplification    : 0.03
% 3.61/1.57  Subsumption          : 0.11
% 3.61/1.57  Abstraction          : 0.03
% 3.61/1.57  MUC search           : 0.00
% 3.61/1.57  Cooper               : 0.00
% 3.61/1.57  Total                : 0.96
% 3.61/1.57  Index Insertion      : 0.00
% 3.61/1.57  Index Deletion       : 0.00
% 3.61/1.57  Index Matching       : 0.00
% 3.61/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
