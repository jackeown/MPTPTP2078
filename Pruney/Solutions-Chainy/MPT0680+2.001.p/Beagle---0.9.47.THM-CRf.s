%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:25 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  57 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ! [B,C] : k9_relat_1(A,k6_subset_1(B,C)) = k6_subset_1(k9_relat_1(A,B),k9_relat_1(A,C))
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B,C] : k9_relat_1(A,k3_xboole_0(B,C)) = k3_xboole_0(k9_relat_1(A,B),k9_relat_1(A,C))
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).

tff(c_8,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_10,C_11] : k6_subset_1(k9_relat_1('#skF_3',B_10),k9_relat_1('#skF_3',C_11)) = k9_relat_1('#skF_3',k6_subset_1(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [B_16,C_17] : k6_subset_1(k9_relat_1('#skF_3',B_16),k9_relat_1('#skF_3',C_17)) = k9_relat_1('#skF_3',k4_xboole_0(B_16,C_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_68,plain,(
    ! [B_20,C_21] : k4_xboole_0(k9_relat_1('#skF_3',B_20),k9_relat_1('#skF_3',C_21)) = k9_relat_1('#skF_3',k4_xboole_0(B_20,C_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_142,plain,(
    ! [B_26,C_27] : k4_xboole_0(k9_relat_1('#skF_3',B_26),k9_relat_1('#skF_3',k4_xboole_0(B_26,C_27))) = k3_xboole_0(k9_relat_1('#skF_3',B_26),k9_relat_1('#skF_3',C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_46,plain,(
    ! [B_16,C_17] : k4_xboole_0(k9_relat_1('#skF_3',B_16),k9_relat_1('#skF_3',C_17)) = k9_relat_1('#skF_3',k4_xboole_0(B_16,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_154,plain,(
    ! [B_26,C_27] : k9_relat_1('#skF_3',k4_xboole_0(B_26,k4_xboole_0(B_26,C_27))) = k3_xboole_0(k9_relat_1('#skF_3',B_26),k9_relat_1('#skF_3',C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_46])).

tff(c_184,plain,(
    ! [B_26,C_27] : k3_xboole_0(k9_relat_1('#skF_3',B_26),k9_relat_1('#skF_3',C_27)) = k9_relat_1('#skF_3',k3_xboole_0(B_26,C_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_207,plain,(
    ! [A_30] :
      ( v2_funct_1(A_30)
      | k3_xboole_0(k9_relat_1(A_30,'#skF_1'(A_30)),k9_relat_1(A_30,'#skF_2'(A_30))) != k9_relat_1(A_30,k3_xboole_0('#skF_1'(A_30),'#skF_2'(A_30)))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_211,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_207])).

tff(c_214,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1 > #skF_3
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.89/1.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_48, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B, C]: (k9_relat_1(A, k6_subset_1(B, C)) = k6_subset_1(k9_relat_1(A, B), k9_relat_1(A, C)))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_funct_1)).
% 1.89/1.22  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.89/1.22  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.89/1.22  tff(f_38, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B, C]: (k9_relat_1(A, k3_xboole_0(B, C)) = k3_xboole_0(k9_relat_1(A, B), k9_relat_1(A, C)))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_funct_1)).
% 1.89/1.22  tff(c_8, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.22  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.22  tff(c_10, plain, (![B_10, C_11]: (k6_subset_1(k9_relat_1('#skF_3', B_10), k9_relat_1('#skF_3', C_11))=k9_relat_1('#skF_3', k6_subset_1(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_40, plain, (![B_16, C_17]: (k6_subset_1(k9_relat_1('#skF_3', B_16), k9_relat_1('#skF_3', C_17))=k9_relat_1('#skF_3', k4_xboole_0(B_16, C_17)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.89/1.22  tff(c_68, plain, (![B_20, C_21]: (k4_xboole_0(k9_relat_1('#skF_3', B_20), k9_relat_1('#skF_3', C_21))=k9_relat_1('#skF_3', k4_xboole_0(B_20, C_21)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 1.89/1.22  tff(c_142, plain, (![B_26, C_27]: (k4_xboole_0(k9_relat_1('#skF_3', B_26), k9_relat_1('#skF_3', k4_xboole_0(B_26, C_27)))=k3_xboole_0(k9_relat_1('#skF_3', B_26), k9_relat_1('#skF_3', C_27)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 1.89/1.22  tff(c_46, plain, (![B_16, C_17]: (k4_xboole_0(k9_relat_1('#skF_3', B_16), k9_relat_1('#skF_3', C_17))=k9_relat_1('#skF_3', k4_xboole_0(B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 1.89/1.22  tff(c_154, plain, (![B_26, C_27]: (k9_relat_1('#skF_3', k4_xboole_0(B_26, k4_xboole_0(B_26, C_27)))=k3_xboole_0(k9_relat_1('#skF_3', B_26), k9_relat_1('#skF_3', C_27)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_46])).
% 1.89/1.22  tff(c_184, plain, (![B_26, C_27]: (k3_xboole_0(k9_relat_1('#skF_3', B_26), k9_relat_1('#skF_3', C_27))=k9_relat_1('#skF_3', k3_xboole_0(B_26, C_27)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_154])).
% 1.89/1.22  tff(c_207, plain, (![A_30]: (v2_funct_1(A_30) | k3_xboole_0(k9_relat_1(A_30, '#skF_1'(A_30)), k9_relat_1(A_30, '#skF_2'(A_30)))!=k9_relat_1(A_30, k3_xboole_0('#skF_1'(A_30), '#skF_2'(A_30))) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.89/1.22  tff(c_211, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_207])).
% 1.89/1.22  tff(c_214, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_211])).
% 1.89/1.22  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_214])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 50
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 0
% 1.89/1.22  #Demod        : 27
% 1.89/1.22  #Tautology    : 27
% 1.89/1.22  #SimpNegUnit  : 1
% 1.89/1.22  #BackRed      : 1
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.28
% 1.89/1.22  Parsing              : 0.15
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.17
% 1.89/1.22  Inferencing          : 0.06
% 1.89/1.22  Reduction            : 0.07
% 1.89/1.22  Demodulation         : 0.05
% 1.89/1.22  BG Simplification    : 0.01
% 1.89/1.22  Subsumption          : 0.02
% 1.89/1.22  Abstraction          : 0.01
% 1.89/1.22  MUC search           : 0.00
% 1.89/1.22  Cooper               : 0.00
% 1.89/1.22  Total                : 0.47
% 1.89/1.22  Index Insertion      : 0.00
% 1.89/1.22  Index Deletion       : 0.00
% 1.89/1.22  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
