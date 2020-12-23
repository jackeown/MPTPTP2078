%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   36 (  77 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 183 expanded)
%              Number of equality atoms :   13 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(c_14,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_47,plain,(
    ! [A_10] :
      ( k4_relat_1(A_10) = k2_funct_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_57,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_53])).

tff(c_8,plain,(
    ! [A_4] :
      ( v1_funct_1(k4_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,
    ( v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_8])).

tff(c_71,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_61])).

tff(c_4,plain,(
    ! [A_2] :
      ( k4_relat_1(k4_relat_1(A_2)) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_4])).

tff(c_73,plain,(
    k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_75,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67])).

tff(c_12,plain,(
    ! [A_5] :
      ( v2_funct_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [A_12] :
      ( k4_relat_1(k2_funct_1(A_12)) = k2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_113,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = k2_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_110])).

tff(c_116,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_71,c_73,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:59:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_1
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.64/1.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.64/1.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.64/1.13  
% 1.64/1.14  tff(f_68, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 1.64/1.14  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 1.64/1.14  tff(f_51, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 1.64/1.14  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 1.64/1.14  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.64/1.14  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 1.64/1.14  tff(c_14, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.64/1.14  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.64/1.14  tff(c_18, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.64/1.14  tff(c_16, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.64/1.14  tff(c_47, plain, (![A_10]: (k4_relat_1(A_10)=k2_funct_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.14  tff(c_53, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_47])).
% 1.64/1.14  tff(c_57, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_53])).
% 1.64/1.14  tff(c_8, plain, (![A_4]: (v1_funct_1(k4_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.14  tff(c_61, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_8])).
% 1.64/1.14  tff(c_71, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_61])).
% 1.64/1.14  tff(c_4, plain, (![A_2]: (k4_relat_1(k4_relat_1(A_2))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.14  tff(c_64, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_4])).
% 1.64/1.14  tff(c_73, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_64])).
% 1.64/1.14  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.14  tff(c_67, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 1.64/1.14  tff(c_75, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 1.64/1.14  tff(c_12, plain, (![A_5]: (v2_funct_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.64/1.14  tff(c_110, plain, (![A_12]: (k4_relat_1(k2_funct_1(A_12))=k2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_12, c_47])).
% 1.64/1.14  tff(c_113, plain, (k4_relat_1(k2_funct_1('#skF_1'))=k2_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_75, c_110])).
% 1.64/1.14  tff(c_116, plain, (k2_funct_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_71, c_73, c_113])).
% 1.64/1.14  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_116])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 22
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 1
% 1.64/1.14  #Demod        : 32
% 1.64/1.14  #Tautology    : 14
% 1.64/1.14  #SimpNegUnit  : 1
% 1.64/1.14  #BackRed      : 0
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.14  Preprocessing        : 0.28
% 1.64/1.14  Parsing              : 0.15
% 1.64/1.14  CNF conversion       : 0.02
% 1.64/1.14  Main loop            : 0.11
% 1.64/1.14  Inferencing          : 0.05
% 1.64/1.14  Reduction            : 0.03
% 1.64/1.14  Demodulation         : 0.03
% 1.64/1.14  BG Simplification    : 0.01
% 1.64/1.14  Subsumption          : 0.02
% 1.64/1.14  Abstraction          : 0.01
% 1.64/1.14  MUC search           : 0.00
% 1.64/1.14  Cooper               : 0.00
% 1.64/1.14  Total                : 0.42
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.64/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
