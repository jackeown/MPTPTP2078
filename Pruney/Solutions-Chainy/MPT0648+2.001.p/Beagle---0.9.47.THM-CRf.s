%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 106 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
            & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_8,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_33,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_5] :
      ( k4_relat_1(A_5) = k2_funct_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_40,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_37])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_51,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_51])).

tff(c_54,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_60,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k2_funct_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_66,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2])).

tff(c_79,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_73])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.44  
% 1.96/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.44  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.96/1.44  
% 1.96/1.44  %Foreground sorts:
% 1.96/1.44  
% 1.96/1.44  
% 1.96/1.44  %Background operators:
% 1.96/1.44  
% 1.96/1.44  
% 1.96/1.44  %Foreground operators:
% 1.96/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.96/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.96/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.44  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.44  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.96/1.44  
% 2.07/1.46  tff(f_50, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.07/1.46  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.07/1.46  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.07/1.46  tff(c_8, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.46  tff(c_33, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_8])).
% 2.07/1.46  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.46  tff(c_12, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.46  tff(c_10, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.46  tff(c_34, plain, (![A_5]: (k4_relat_1(A_5)=k2_funct_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.46  tff(c_37, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_34])).
% 2.07/1.46  tff(c_40, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_37])).
% 2.07/1.46  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.46  tff(c_44, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 2.07/1.46  tff(c_51, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 2.07/1.46  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_51])).
% 2.07/1.46  tff(c_54, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_8])).
% 2.07/1.46  tff(c_60, plain, (![A_6]: (k4_relat_1(A_6)=k2_funct_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.46  tff(c_63, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.07/1.46  tff(c_66, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_63])).
% 2.07/1.46  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.46  tff(c_73, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_66, c_2])).
% 2.07/1.46  tff(c_79, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_73])).
% 2.07/1.46  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_79])).
% 2.07/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.46  
% 2.07/1.46  Inference rules
% 2.07/1.46  ----------------------
% 2.07/1.46  #Ref     : 0
% 2.07/1.46  #Sup     : 16
% 2.07/1.46  #Fact    : 0
% 2.07/1.46  #Define  : 0
% 2.07/1.46  #Split   : 1
% 2.07/1.46  #Chain   : 0
% 2.07/1.46  #Close   : 0
% 2.07/1.46  
% 2.07/1.46  Ordering : KBO
% 2.07/1.46  
% 2.07/1.46  Simplification rules
% 2.07/1.46  ----------------------
% 2.07/1.46  #Subsume      : 0
% 2.07/1.46  #Demod        : 8
% 2.07/1.46  #Tautology    : 9
% 2.07/1.46  #SimpNegUnit  : 2
% 2.07/1.46  #BackRed      : 0
% 2.07/1.46  
% 2.07/1.46  #Partial instantiations: 0
% 2.07/1.46  #Strategies tried      : 1
% 2.07/1.46  
% 2.07/1.46  Timing (in seconds)
% 2.07/1.46  ----------------------
% 2.09/1.46  Preprocessing        : 0.42
% 2.09/1.46  Parsing              : 0.21
% 2.09/1.46  CNF conversion       : 0.03
% 2.09/1.46  Main loop            : 0.16
% 2.09/1.46  Inferencing          : 0.07
% 2.09/1.46  Reduction            : 0.04
% 2.09/1.46  Demodulation         : 0.03
% 2.09/1.46  BG Simplification    : 0.01
% 2.09/1.46  Subsumption          : 0.02
% 2.09/1.46  Abstraction          : 0.01
% 2.09/1.46  MUC search           : 0.00
% 2.09/1.46  Cooper               : 0.00
% 2.09/1.46  Total                : 0.61
% 2.09/1.46  Index Insertion      : 0.00
% 2.09/1.46  Index Deletion       : 0.00
% 2.09/1.46  Index Matching       : 0.00
% 2.09/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
