%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  53 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k4_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,k4_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_4,B_5] : k6_subset_1(A_4,B_5) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k6_subset_1(B_12,k7_relat_1(B_12,A_11))) = k6_subset_1(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [B_22,A_23] :
      ( k1_relat_1(k4_xboole_0(B_22,k7_relat_1(B_22,A_23))) = k4_xboole_0(k1_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_10])).

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( k7_relat_1(A_8,B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,k1_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [B_24,A_25,B_26] :
      ( k7_relat_1(k4_xboole_0(B_24,k7_relat_1(B_24,A_25)),B_26) = k1_xboole_0
      | ~ r1_xboole_0(B_26,k4_xboole_0(k1_relat_1(B_24),A_25))
      | ~ v1_relat_1(k4_xboole_0(B_24,k7_relat_1(B_24,A_25)))
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_8])).

tff(c_50,plain,(
    ! [B_27,B_28,A_29] :
      ( k7_relat_1(k4_xboole_0(B_27,k7_relat_1(B_27,B_28)),A_29) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_27,k7_relat_1(B_27,B_28)))
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_55,plain,(
    ! [A_30,B_31,A_32] :
      ( k7_relat_1(k4_xboole_0(A_30,k7_relat_1(A_30,B_31)),A_32) = k1_xboole_0
      | ~ r1_tarski(A_32,B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_12,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_67,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_18])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.14  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.63/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.15  
% 1.63/1.15  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 1.63/1.15  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 1.63/1.15  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.63/1.15  tff(f_31, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.63/1.15  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 1.63/1.15  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 1.63/1.15  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k4_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.15  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, k4_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_4, plain, (![A_4, B_5]: (k6_subset_1(A_4, B_5)=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.15  tff(c_10, plain, (![B_12, A_11]: (k1_relat_1(k6_subset_1(B_12, k7_relat_1(B_12, A_11)))=k6_subset_1(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.15  tff(c_31, plain, (![B_22, A_23]: (k1_relat_1(k4_xboole_0(B_22, k7_relat_1(B_22, A_23)))=k4_xboole_0(k1_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_10])).
% 1.63/1.15  tff(c_8, plain, (![A_8, B_10]: (k7_relat_1(A_8, B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, k1_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.15  tff(c_43, plain, (![B_24, A_25, B_26]: (k7_relat_1(k4_xboole_0(B_24, k7_relat_1(B_24, A_25)), B_26)=k1_xboole_0 | ~r1_xboole_0(B_26, k4_xboole_0(k1_relat_1(B_24), A_25)) | ~v1_relat_1(k4_xboole_0(B_24, k7_relat_1(B_24, A_25))) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_31, c_8])).
% 1.63/1.15  tff(c_50, plain, (![B_27, B_28, A_29]: (k7_relat_1(k4_xboole_0(B_27, k7_relat_1(B_27, B_28)), A_29)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_27, k7_relat_1(B_27, B_28))) | ~v1_relat_1(B_27) | ~r1_tarski(A_29, B_28))), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.63/1.15  tff(c_55, plain, (![A_30, B_31, A_32]: (k7_relat_1(k4_xboole_0(A_30, k7_relat_1(A_30, B_31)), A_32)=k1_xboole_0 | ~r1_tarski(A_32, B_31) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.63/1.15  tff(c_12, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_18, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 1.63/1.15  tff(c_67, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_55, c_18])).
% 1.63/1.15  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_67])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 14
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 0
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 1
% 1.63/1.15  #Demod        : 5
% 1.63/1.15  #Tautology    : 5
% 1.63/1.15  #SimpNegUnit  : 0
% 1.63/1.15  #BackRed      : 0
% 1.63/1.15  
% 1.63/1.15  #Partial instantiations: 0
% 1.63/1.15  #Strategies tried      : 1
% 1.63/1.15  
% 1.63/1.15  Timing (in seconds)
% 1.63/1.15  ----------------------
% 1.63/1.16  Preprocessing        : 0.27
% 1.63/1.16  Parsing              : 0.14
% 1.63/1.16  CNF conversion       : 0.02
% 1.63/1.16  Main loop            : 0.10
% 1.63/1.16  Inferencing          : 0.04
% 1.63/1.16  Reduction            : 0.03
% 1.63/1.16  Demodulation         : 0.02
% 1.63/1.16  BG Simplification    : 0.01
% 1.63/1.16  Subsumption          : 0.01
% 1.63/1.16  Abstraction          : 0.01
% 1.63/1.16  MUC search           : 0.00
% 1.63/1.16  Cooper               : 0.00
% 1.63/1.16  Total                : 0.39
% 1.63/1.16  Index Insertion      : 0.00
% 1.63/1.16  Index Deletion       : 0.00
% 1.63/1.16  Index Matching       : 0.00
% 1.63/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
