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
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   36 (  66 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 186 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    ! [A_13,B_14] :
      ( v2_funct_1(A_13)
      | k6_relat_1(k1_relat_1(A_13)) != k5_relat_1(A_13,B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_15] :
      ( v2_funct_1(k2_funct_1(A_15))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_15))) != k6_relat_1(k2_relat_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15)
      | ~ v1_funct_1(k2_funct_1(A_15))
      | ~ v1_relat_1(k2_funct_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_61])).

tff(c_74,plain,(
    ! [A_16] :
      ( v2_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(k2_funct_1(A_16))
      | ~ v1_relat_1(k2_funct_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_16,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_77,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_80,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_77])).

tff(c_81,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_84,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_84])).

tff(c_89,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_93,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.69/1.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.69/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.14  
% 1.69/1.15  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 1.69/1.15  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.69/1.15  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 1.69/1.15  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 1.69/1.15  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 1.69/1.15  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.69/1.15  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.69/1.15  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.15  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.15  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.69/1.15  tff(c_10, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.15  tff(c_12, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.69/1.15  tff(c_61, plain, (![A_13, B_14]: (v2_funct_1(A_13) | k6_relat_1(k1_relat_1(A_13))!=k5_relat_1(A_13, B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.15  tff(c_69, plain, (![A_15]: (v2_funct_1(k2_funct_1(A_15)) | k6_relat_1(k1_relat_1(k2_funct_1(A_15)))!=k6_relat_1(k2_relat_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15) | ~v1_funct_1(k2_funct_1(A_15)) | ~v1_relat_1(k2_funct_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_12, c_61])).
% 1.69/1.15  tff(c_74, plain, (![A_16]: (v2_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(k2_funct_1(A_16)) | ~v1_relat_1(k2_funct_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 1.69/1.15  tff(c_16, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.69/1.15  tff(c_77, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_74, c_16])).
% 1.69/1.15  tff(c_80, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_77])).
% 1.69/1.15  tff(c_81, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.69/1.15  tff(c_84, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_81])).
% 1.69/1.15  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_84])).
% 1.69/1.15  tff(c_89, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_80])).
% 1.69/1.15  tff(c_93, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_89])).
% 1.69/1.15  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_93])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 15
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 1
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 2
% 1.69/1.15  #Demod        : 7
% 1.69/1.15  #Tautology    : 9
% 1.69/1.15  #SimpNegUnit  : 0
% 1.69/1.15  #BackRed      : 0
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.15  Timing (in seconds)
% 1.69/1.15  ----------------------
% 1.69/1.15  Preprocessing        : 0.28
% 1.69/1.15  Parsing              : 0.15
% 1.69/1.15  CNF conversion       : 0.02
% 1.69/1.15  Main loop            : 0.12
% 1.69/1.15  Inferencing          : 0.05
% 1.69/1.15  Reduction            : 0.03
% 1.69/1.15  Demodulation         : 0.02
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.02
% 1.69/1.15  Abstraction          : 0.01
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.42
% 1.69/1.15  Index Insertion      : 0.00
% 1.69/1.15  Index Deletion       : 0.00
% 1.69/1.15  Index Matching       : 0.00
% 1.69/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
