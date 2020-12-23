%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_14,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    v2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8])).

tff(c_10,plain,(
    ! [B_5,A_3] :
      ( r1_tarski(k2_relat_1(B_5),k1_relat_1(A_3))
      | k1_relat_1(k5_relat_1(B_5,A_3)) != k1_relat_1(B_5)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [B_16,A_17] :
      ( v2_funct_1(B_16)
      | ~ r1_tarski(k2_relat_1(B_16),k1_relat_1(A_17))
      | ~ v2_funct_1(k5_relat_1(B_16,A_17))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,(
    ! [B_24,A_25] :
      ( v2_funct_1(B_24)
      | ~ v2_funct_1(k5_relat_1(B_24,A_25))
      | k1_relat_1(k5_relat_1(B_24,A_25)) != k1_relat_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_132,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_129])).

tff(c_135,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24,c_22,c_48,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.91/1.25  
% 1.91/1.25  %Foreground sorts:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Background operators:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Foreground operators:
% 1.91/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.91/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.25  
% 1.91/1.26  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 1.91/1.26  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.91/1.26  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.91/1.26  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 1.91/1.26  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 1.91/1.26  tff(c_14, plain, (~v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_16, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.91/1.26  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.26  tff(c_48, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2])).
% 1.91/1.26  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.26  tff(c_55, plain, (v2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8])).
% 1.91/1.26  tff(c_10, plain, (![B_5, A_3]: (r1_tarski(k2_relat_1(B_5), k1_relat_1(A_3)) | k1_relat_1(k5_relat_1(B_5, A_3))!=k1_relat_1(B_5) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.26  tff(c_88, plain, (![B_16, A_17]: (v2_funct_1(B_16) | ~r1_tarski(k2_relat_1(B_16), k1_relat_1(A_17)) | ~v2_funct_1(k5_relat_1(B_16, A_17)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.26  tff(c_129, plain, (![B_24, A_25]: (v2_funct_1(B_24) | ~v2_funct_1(k5_relat_1(B_24, A_25)) | k1_relat_1(k5_relat_1(B_24, A_25))!=k1_relat_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_10, c_88])).
% 1.91/1.26  tff(c_132, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_55, c_129])).
% 1.91/1.26  tff(c_135, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_24, c_22, c_48, c_132])).
% 1.91/1.26  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_135])).
% 1.91/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  Inference rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Ref     : 0
% 1.91/1.26  #Sup     : 27
% 1.91/1.26  #Fact    : 0
% 1.91/1.26  #Define  : 0
% 1.91/1.26  #Split   : 1
% 1.91/1.26  #Chain   : 0
% 1.91/1.26  #Close   : 0
% 1.91/1.26  
% 1.91/1.26  Ordering : KBO
% 1.91/1.26  
% 1.91/1.26  Simplification rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Subsume      : 0
% 1.91/1.26  #Demod        : 20
% 1.91/1.26  #Tautology    : 12
% 1.91/1.26  #SimpNegUnit  : 1
% 1.91/1.26  #BackRed      : 0
% 1.91/1.26  
% 1.91/1.26  #Partial instantiations: 0
% 1.91/1.26  #Strategies tried      : 1
% 1.91/1.26  
% 1.91/1.26  Timing (in seconds)
% 1.91/1.26  ----------------------
% 1.91/1.27  Preprocessing        : 0.29
% 1.91/1.27  Parsing              : 0.17
% 1.91/1.27  CNF conversion       : 0.02
% 1.91/1.27  Main loop            : 0.16
% 1.91/1.27  Inferencing          : 0.06
% 1.91/1.27  Reduction            : 0.05
% 1.91/1.27  Demodulation         : 0.04
% 1.91/1.27  BG Simplification    : 0.01
% 1.91/1.27  Subsumption          : 0.03
% 1.91/1.27  Abstraction          : 0.01
% 1.91/1.27  MUC search           : 0.00
% 1.91/1.27  Cooper               : 0.00
% 1.91/1.27  Total                : 0.48
% 1.91/1.27  Index Insertion      : 0.00
% 1.91/1.27  Index Deletion       : 0.00
% 1.91/1.27  Index Matching       : 0.00
% 1.91/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
