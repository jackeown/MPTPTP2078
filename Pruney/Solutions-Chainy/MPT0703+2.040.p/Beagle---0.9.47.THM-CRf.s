%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  84 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_14])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k10_relat_1(C_12,A_10),k10_relat_1(C_12,B_11)) = k10_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_219,plain,(
    ! [C_33,A_34,B_35] :
      ( k4_xboole_0(k10_relat_1(C_33,A_34),k10_relat_1(C_33,B_35)) = k10_relat_1(C_33,k4_xboole_0(A_34,B_35))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_18,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_4])).

tff(c_232,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_54])).

tff(c_246,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_232])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [B_24,A_25] :
      ( k10_relat_1(B_24,A_25) != k1_xboole_0
      | ~ r1_tarski(A_25,k2_relat_1(B_24))
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_693,plain,(
    ! [B_82,A_83,C_84] :
      ( k10_relat_1(B_82,k4_xboole_0(A_83,C_84)) != k1_xboole_0
      | k4_xboole_0(A_83,C_84) = k1_xboole_0
      | ~ v1_relat_1(B_82)
      | ~ r1_tarski(A_83,k2_relat_1(B_82)) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_697,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_693])).

tff(c_716,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22,c_697])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.43  
% 2.50/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.44  
% 2.50/1.44  %Foreground sorts:
% 2.50/1.44  
% 2.50/1.44  
% 2.50/1.44  %Background operators:
% 2.50/1.44  
% 2.50/1.44  
% 2.50/1.44  %Foreground operators:
% 2.50/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.50/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.50/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.44  
% 2.83/1.45  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.83/1.45  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.83/1.45  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.83/1.45  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 2.83/1.45  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.83/1.45  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.83/1.45  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.45  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_50, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_14])).
% 2.83/1.45  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_8, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.45  tff(c_12, plain, (![C_12, A_10, B_11]: (k6_subset_1(k10_relat_1(C_12, A_10), k10_relat_1(C_12, B_11))=k10_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.45  tff(c_219, plain, (![C_33, A_34, B_35]: (k4_xboole_0(k10_relat_1(C_33, A_34), k10_relat_1(C_33, B_35))=k10_relat_1(C_33, k4_xboole_0(A_34, B_35)) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 2.83/1.45  tff(c_18, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.45  tff(c_54, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_4])).
% 2.83/1.45  tff(c_232, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_219, c_54])).
% 2.83/1.45  tff(c_246, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_232])).
% 2.83/1.45  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.45  tff(c_92, plain, (![B_24, A_25]: (k10_relat_1(B_24, A_25)!=k1_xboole_0 | ~r1_tarski(A_25, k2_relat_1(B_24)) | k1_xboole_0=A_25 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.45  tff(c_693, plain, (![B_82, A_83, C_84]: (k10_relat_1(B_82, k4_xboole_0(A_83, C_84))!=k1_xboole_0 | k4_xboole_0(A_83, C_84)=k1_xboole_0 | ~v1_relat_1(B_82) | ~r1_tarski(A_83, k2_relat_1(B_82)))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.83/1.45  tff(c_697, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_693])).
% 2.83/1.45  tff(c_716, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22, c_697])).
% 2.83/1.45  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_716])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 188
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 3
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 47
% 2.83/1.45  #Demod        : 50
% 2.83/1.45  #Tautology    : 60
% 2.83/1.45  #SimpNegUnit  : 2
% 2.83/1.45  #BackRed      : 2
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.27
% 2.83/1.45  Parsing              : 0.14
% 2.83/1.45  CNF conversion       : 0.02
% 2.83/1.45  Main loop            : 0.41
% 2.83/1.45  Inferencing          : 0.15
% 2.83/1.45  Reduction            : 0.11
% 2.83/1.45  Demodulation         : 0.08
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.09
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.71
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
