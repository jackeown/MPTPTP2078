%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_10,A_8,B_9] :
      ( k6_subset_1(k7_relat_1(C_10,A_8),k7_relat_1(C_10,B_9)) = k7_relat_1(C_10,k6_subset_1(A_8,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [C_29,A_30,B_31] :
      ( k4_xboole_0(k7_relat_1(C_29,A_30),k7_relat_1(C_29,B_31)) = k7_relat_1(C_29,k4_xboole_0(A_30,B_31))
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_12])).

tff(c_161,plain,(
    ! [A_39,B_40] :
      ( k7_relat_1(A_39,k4_xboole_0(k1_relat_1(A_39),B_40)) = k4_xboole_0(A_39,k7_relat_1(A_39,B_40))
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_102])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [B_23,A_24] :
      ( k1_relat_1(k7_relat_1(B_23,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [B_23,A_3,C_5] :
      ( k1_relat_1(k7_relat_1(B_23,k4_xboole_0(A_3,C_5))) = k4_xboole_0(A_3,C_5)
      | ~ v1_relat_1(B_23)
      | ~ r1_tarski(A_3,k1_relat_1(B_23)) ) ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_167,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k4_xboole_0(A_39,k7_relat_1(A_39,B_40))) = k4_xboole_0(k1_relat_1(A_39),B_40)
      | ~ v1_relat_1(A_39)
      | ~ r1_tarski(k1_relat_1(A_39),k1_relat_1(A_39))
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_63])).

tff(c_190,plain,(
    ! [A_41,B_42] :
      ( k1_relat_1(k4_xboole_0(A_41,k7_relat_1(A_41,B_42))) = k4_xboole_0(k1_relat_1(A_41),B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_167])).

tff(c_18,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_205,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_21])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:43:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.25  
% 1.67/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.25  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.67/1.25  
% 1.67/1.25  %Foreground sorts:
% 1.67/1.25  
% 1.67/1.25  
% 1.67/1.25  %Background operators:
% 1.67/1.25  
% 1.67/1.25  
% 1.67/1.25  %Foreground operators:
% 1.67/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.67/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.25  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.67/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.25  
% 1.67/1.26  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 1.67/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.67/1.26  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.67/1.26  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.67/1.26  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 1.67/1.26  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.67/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.67/1.26  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.26  tff(c_16, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.26  tff(c_10, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.26  tff(c_12, plain, (![C_10, A_8, B_9]: (k6_subset_1(k7_relat_1(C_10, A_8), k7_relat_1(C_10, B_9))=k7_relat_1(C_10, k6_subset_1(A_8, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.26  tff(c_102, plain, (![C_29, A_30, B_31]: (k4_xboole_0(k7_relat_1(C_29, A_30), k7_relat_1(C_29, B_31))=k7_relat_1(C_29, k4_xboole_0(A_30, B_31)) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_12])).
% 1.67/1.26  tff(c_161, plain, (![A_39, B_40]: (k7_relat_1(A_39, k4_xboole_0(k1_relat_1(A_39), B_40))=k4_xboole_0(A_39, k7_relat_1(A_39, B_40)) | ~v1_relat_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_16, c_102])).
% 1.67/1.26  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.26  tff(c_54, plain, (![B_23, A_24]: (k1_relat_1(k7_relat_1(B_23, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.26  tff(c_63, plain, (![B_23, A_3, C_5]: (k1_relat_1(k7_relat_1(B_23, k4_xboole_0(A_3, C_5)))=k4_xboole_0(A_3, C_5) | ~v1_relat_1(B_23) | ~r1_tarski(A_3, k1_relat_1(B_23)))), inference(resolution, [status(thm)], [c_8, c_54])).
% 1.67/1.26  tff(c_167, plain, (![A_39, B_40]: (k1_relat_1(k4_xboole_0(A_39, k7_relat_1(A_39, B_40)))=k4_xboole_0(k1_relat_1(A_39), B_40) | ~v1_relat_1(A_39) | ~r1_tarski(k1_relat_1(A_39), k1_relat_1(A_39)) | ~v1_relat_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_161, c_63])).
% 1.67/1.26  tff(c_190, plain, (![A_41, B_42]: (k1_relat_1(k4_xboole_0(A_41, k7_relat_1(A_41, B_42)))=k4_xboole_0(k1_relat_1(A_41), B_42) | ~v1_relat_1(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_167])).
% 1.67/1.26  tff(c_18, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.26  tff(c_21, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 1.67/1.26  tff(c_205, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_190, c_21])).
% 1.67/1.26  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_205])).
% 1.67/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.26  
% 1.67/1.26  Inference rules
% 1.67/1.26  ----------------------
% 1.67/1.26  #Ref     : 0
% 1.67/1.26  #Sup     : 50
% 1.67/1.26  #Fact    : 0
% 1.67/1.26  #Define  : 0
% 1.67/1.26  #Split   : 0
% 1.67/1.26  #Chain   : 0
% 1.67/1.26  #Close   : 0
% 1.67/1.26  
% 1.67/1.26  Ordering : KBO
% 1.67/1.26  
% 1.67/1.26  Simplification rules
% 1.67/1.26  ----------------------
% 1.67/1.26  #Subsume      : 0
% 1.67/1.26  #Demod        : 8
% 1.67/1.26  #Tautology    : 17
% 1.67/1.26  #SimpNegUnit  : 0
% 1.67/1.26  #BackRed      : 0
% 1.67/1.26  
% 1.67/1.26  #Partial instantiations: 0
% 1.67/1.26  #Strategies tried      : 1
% 1.67/1.26  
% 1.67/1.26  Timing (in seconds)
% 1.67/1.26  ----------------------
% 1.67/1.27  Preprocessing        : 0.29
% 1.67/1.27  Parsing              : 0.16
% 1.67/1.27  CNF conversion       : 0.02
% 1.67/1.27  Main loop            : 0.17
% 1.67/1.27  Inferencing          : 0.07
% 1.67/1.27  Reduction            : 0.04
% 1.67/1.27  Demodulation         : 0.03
% 1.67/1.27  BG Simplification    : 0.01
% 1.67/1.27  Subsumption          : 0.04
% 1.67/1.27  Abstraction          : 0.01
% 1.67/1.27  MUC search           : 0.00
% 1.67/1.27  Cooper               : 0.00
% 1.67/1.27  Total                : 0.48
% 1.67/1.27  Index Insertion      : 0.00
% 1.67/1.27  Index Deletion       : 0.00
% 1.67/1.27  Index Matching       : 0.00
% 1.67/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
