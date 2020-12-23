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
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  29 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_11,B_12)),k1_relat_1(A_11))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_1,B_2)),k1_relat_1(B_2))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_13,B_14)),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_29])).

tff(c_10,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_10])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.05  
% 1.56/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.06  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.56/1.06  
% 1.56/1.06  %Foreground sorts:
% 1.56/1.06  
% 1.56/1.06  
% 1.56/1.06  %Background operators:
% 1.56/1.06  
% 1.56/1.06  
% 1.56/1.06  %Foreground operators:
% 1.56/1.06  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.56/1.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.56/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.56/1.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.56/1.06  
% 1.56/1.07  tff(f_47, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_funct_1)).
% 1.56/1.07  tff(f_40, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.56/1.07  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.56/1.07  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 1.56/1.07  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.56/1.07  tff(c_6, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.07  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.07  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(k1_relat_1(k5_relat_1(A_11, B_12)), k1_relat_1(A_11)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.56/1.07  tff(c_29, plain, (![A_1, B_2]: (r1_tarski(k1_relat_1(k8_relat_1(A_1, B_2)), k1_relat_1(B_2)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(B_2) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_26])).
% 1.56/1.07  tff(c_32, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k8_relat_1(A_13, B_14)), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_29])).
% 1.56/1.07  tff(c_10, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.56/1.07  tff(c_35, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_10])).
% 1.56/1.07  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_35])).
% 1.56/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  Inference rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Ref     : 0
% 1.56/1.07  #Sup     : 4
% 1.56/1.07  #Fact    : 0
% 1.56/1.07  #Define  : 0
% 1.56/1.07  #Split   : 0
% 1.56/1.07  #Chain   : 0
% 1.56/1.07  #Close   : 0
% 1.56/1.07  
% 1.56/1.07  Ordering : KBO
% 1.56/1.07  
% 1.56/1.07  Simplification rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Subsume      : 0
% 1.56/1.07  #Demod        : 2
% 1.56/1.07  #Tautology    : 2
% 1.56/1.07  #SimpNegUnit  : 0
% 1.56/1.07  #BackRed      : 0
% 1.56/1.07  
% 1.56/1.07  #Partial instantiations: 0
% 1.56/1.07  #Strategies tried      : 1
% 1.56/1.07  
% 1.56/1.07  Timing (in seconds)
% 1.56/1.07  ----------------------
% 1.56/1.07  Preprocessing        : 0.25
% 1.56/1.07  Parsing              : 0.14
% 1.56/1.07  CNF conversion       : 0.02
% 1.56/1.07  Main loop            : 0.07
% 1.56/1.07  Inferencing          : 0.03
% 1.56/1.07  Reduction            : 0.02
% 1.56/1.07  Demodulation         : 0.02
% 1.56/1.08  BG Simplification    : 0.01
% 1.56/1.08  Subsumption          : 0.01
% 1.56/1.08  Abstraction          : 0.00
% 1.56/1.08  MUC search           : 0.00
% 1.56/1.08  Cooper               : 0.00
% 1.56/1.08  Total                : 0.35
% 1.56/1.08  Index Insertion      : 0.00
% 1.56/1.08  Index Deletion       : 0.00
% 1.56/1.08  Index Matching       : 0.00
% 1.56/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
