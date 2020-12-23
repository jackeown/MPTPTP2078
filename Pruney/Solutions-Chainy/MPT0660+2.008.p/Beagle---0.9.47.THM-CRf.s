%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   33 (  63 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 109 expanded)
%              Number of equality atoms :   23 (  41 expanded)
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    ! [A_1] :
      ( k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_50,plain,(
    ! [A_1] : k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_60,plain,(
    ! [A_16,B_17] :
      ( v2_funct_1(A_16)
      | k6_relat_1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [A_1] :
      ( v2_funct_1(k6_relat_1(A_1))
      | k6_relat_1(k1_relat_1(k6_relat_1(A_1))) != k6_relat_1(A_1)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_68,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_8,c_10,c_2,c_62])).

tff(c_74,plain,(
    ! [A_19,B_20] :
      ( k2_funct_1(A_19) = B_20
      | k6_relat_1(k2_relat_1(A_19)) != k5_relat_1(B_20,A_19)
      | k2_relat_1(B_20) != k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,(
    ! [A_1] :
      ( k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1)
      | k6_relat_1(k2_relat_1(k6_relat_1(A_1))) != k6_relat_1(A_1)
      | k2_relat_1(k6_relat_1(A_1)) != k1_relat_1(k6_relat_1(A_1))
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_82,plain,(
    ! [A_1] : k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_8,c_10,c_68,c_4,c_2,c_4,c_76])).

tff(c_16,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.73/1.15  
% 1.73/1.15  %Foreground sorts:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Background operators:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Foreground operators:
% 1.73/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.73/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.73/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.15  
% 1.73/1.16  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.73/1.16  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.73/1.16  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.73/1.16  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 1.73/1.16  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 1.73/1.16  tff(f_70, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.73/1.16  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.16  tff(c_10, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.16  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.16  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.16  tff(c_37, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.16  tff(c_46, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.73/1.16  tff(c_50, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 1.73/1.16  tff(c_60, plain, (![A_16, B_17]: (v2_funct_1(A_16) | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.16  tff(c_62, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)) | k6_relat_1(k1_relat_1(k6_relat_1(A_1)))!=k6_relat_1(A_1) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_60])).
% 1.73/1.16  tff(c_68, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_10, c_2, c_62])).
% 1.73/1.16  tff(c_74, plain, (![A_19, B_20]: (k2_funct_1(A_19)=B_20 | k6_relat_1(k2_relat_1(A_19))!=k5_relat_1(B_20, A_19) | k2_relat_1(B_20)!=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.73/1.16  tff(c_76, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1) | k6_relat_1(k2_relat_1(k6_relat_1(A_1)))!=k6_relat_1(A_1) | k2_relat_1(k6_relat_1(A_1))!=k1_relat_1(k6_relat_1(A_1)) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_74])).
% 1.73/1.16  tff(c_82, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_10, c_68, c_4, c_2, c_4, c_76])).
% 1.73/1.16  tff(c_16, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.73/1.16  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 1.73/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  Inference rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Ref     : 0
% 1.73/1.16  #Sup     : 15
% 1.73/1.16  #Fact    : 0
% 1.73/1.16  #Define  : 0
% 1.73/1.16  #Split   : 0
% 1.73/1.16  #Chain   : 0
% 1.73/1.16  #Close   : 0
% 1.73/1.16  
% 1.73/1.16  Ordering : KBO
% 1.73/1.16  
% 1.73/1.16  Simplification rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Subsume      : 0
% 1.73/1.16  #Demod        : 28
% 1.73/1.16  #Tautology    : 8
% 1.73/1.16  #SimpNegUnit  : 0
% 1.73/1.16  #BackRed      : 1
% 1.73/1.16  
% 1.73/1.16  #Partial instantiations: 0
% 1.73/1.16  #Strategies tried      : 1
% 1.73/1.16  
% 1.73/1.16  Timing (in seconds)
% 1.73/1.16  ----------------------
% 1.73/1.16  Preprocessing        : 0.28
% 1.73/1.16  Parsing              : 0.16
% 1.73/1.16  CNF conversion       : 0.02
% 1.73/1.16  Main loop            : 0.12
% 1.73/1.16  Inferencing          : 0.05
% 1.73/1.16  Reduction            : 0.04
% 1.73/1.16  Demodulation         : 0.03
% 1.73/1.16  BG Simplification    : 0.01
% 1.73/1.16  Subsumption          : 0.02
% 1.73/1.16  Abstraction          : 0.01
% 1.73/1.16  MUC search           : 0.00
% 1.73/1.16  Cooper               : 0.00
% 1.73/1.16  Total                : 0.43
% 1.73/1.16  Index Insertion      : 0.00
% 1.73/1.16  Index Deletion       : 0.00
% 1.73/1.16  Index Matching       : 0.00
% 1.73/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
