%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  43 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [C_43,A_44,B_45] :
      ( k2_xboole_0(k9_relat_1(C_43,A_44),k9_relat_1(C_43,B_45)) = k9_relat_1(C_43,k2_xboole_0(A_44,B_45))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,k2_xboole_0(B_23,C_24))
      | ~ r1_tarski(k4_xboole_0(A_22,B_23),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_134,plain,(
    ! [C_43,B_45,A_44] :
      ( r1_tarski(k9_relat_1(C_43,B_45),k9_relat_1(C_43,k2_xboole_0(A_44,B_45)))
      | ~ v1_relat_1(C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_41])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [C_15,A_13,B_14] :
      ( k2_xboole_0(k9_relat_1(C_15,A_13),k9_relat_1(C_15,B_14)) = k9_relat_1(C_15,k2_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_76,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k2_xboole_0(k9_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_6,c_17])).

tff(c_170,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_172,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4,c_170])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:59:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.18  
% 1.98/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.18  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.98/1.18  
% 1.98/1.18  %Foreground sorts:
% 1.98/1.18  
% 1.98/1.18  
% 1.98/1.18  %Background operators:
% 1.98/1.18  
% 1.98/1.18  
% 1.98/1.18  %Foreground operators:
% 1.98/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.98/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.18  
% 1.98/1.19  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 1.98/1.19  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 1.98/1.19  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.98/1.19  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.98/1.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.98/1.19  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.98/1.19  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.98/1.19  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.19  tff(c_113, plain, (![C_43, A_44, B_45]: (k2_xboole_0(k9_relat_1(C_43, A_44), k9_relat_1(C_43, B_45))=k9_relat_1(C_43, k2_xboole_0(A_44, B_45)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.19  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.19  tff(c_37, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, k2_xboole_0(B_23, C_24)) | ~r1_tarski(k4_xboole_0(A_22, B_23), C_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.19  tff(c_41, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.98/1.19  tff(c_134, plain, (![C_43, B_45, A_44]: (r1_tarski(k9_relat_1(C_43, B_45), k9_relat_1(C_43, k2_xboole_0(A_44, B_45))) | ~v1_relat_1(C_43))), inference(superposition, [status(thm), theory('equality')], [c_113, c_41])).
% 1.98/1.19  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.19  tff(c_12, plain, (![C_15, A_13, B_14]: (k2_xboole_0(k9_relat_1(C_15, A_13), k9_relat_1(C_15, B_14))=k9_relat_1(C_15, k2_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.19  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.19  tff(c_10, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.19  tff(c_14, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.19  tff(c_17, plain, (~r1_tarski(k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 1.98/1.19  tff(c_76, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k9_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_17])).
% 1.98/1.19  tff(c_170, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 1.98/1.19  tff(c_172, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', k2_xboole_0('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4, c_170])).
% 1.98/1.19  tff(c_175, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_172])).
% 1.98/1.19  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_175])).
% 1.98/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  Inference rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Ref     : 0
% 1.98/1.19  #Sup     : 38
% 1.98/1.19  #Fact    : 0
% 1.98/1.19  #Define  : 0
% 1.98/1.19  #Split   : 0
% 1.98/1.19  #Chain   : 0
% 1.98/1.19  #Close   : 0
% 1.98/1.19  
% 1.98/1.19  Ordering : KBO
% 1.98/1.19  
% 1.98/1.19  Simplification rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Subsume      : 0
% 1.98/1.19  #Demod        : 8
% 1.98/1.19  #Tautology    : 10
% 1.98/1.19  #SimpNegUnit  : 0
% 1.98/1.19  #BackRed      : 0
% 1.98/1.19  
% 1.98/1.19  #Partial instantiations: 0
% 1.98/1.19  #Strategies tried      : 1
% 1.98/1.19  
% 1.98/1.19  Timing (in seconds)
% 1.98/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.31
% 1.98/1.19  Parsing              : 0.16
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.17
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.05
% 1.98/1.19  Demodulation         : 0.04
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.03
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.50
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
