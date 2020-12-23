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
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

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
      | k6_relat_1(k1_relat_1(A_19)) != k5_relat_1(A_19,B_20)
      | k2_relat_1(A_19) != k1_relat_1(B_20)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,(
    ! [A_1] :
      ( k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1)
      | k6_relat_1(k1_relat_1(k6_relat_1(A_1))) != k6_relat_1(A_1)
      | k2_relat_1(k6_relat_1(A_1)) != k1_relat_1(k6_relat_1(A_1))
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_82,plain,(
    ! [A_1] : k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_8,c_10,c_68,c_4,c_2,c_2,c_76])).

tff(c_16,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 18:06:08 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.67/1.09  
% 1.67/1.09  %Foreground sorts:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Background operators:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Foreground operators:
% 1.67/1.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.67/1.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.67/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.09  
% 1.67/1.10  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.67/1.10  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.67/1.10  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.67/1.10  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 1.67/1.10  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 1.67/1.10  tff(f_70, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 1.67/1.10  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.10  tff(c_10, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.10  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.10  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.10  tff(c_37, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.10  tff(c_46, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.67/1.10  tff(c_50, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 1.67/1.10  tff(c_60, plain, (![A_16, B_17]: (v2_funct_1(A_16) | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.10  tff(c_62, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)) | k6_relat_1(k1_relat_1(k6_relat_1(A_1)))!=k6_relat_1(A_1) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_60])).
% 1.67/1.10  tff(c_68, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_10, c_2, c_62])).
% 1.67/1.10  tff(c_74, plain, (![A_19, B_20]: (k2_funct_1(A_19)=B_20 | k6_relat_1(k1_relat_1(A_19))!=k5_relat_1(A_19, B_20) | k2_relat_1(A_19)!=k1_relat_1(B_20) | ~v2_funct_1(A_19) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.10  tff(c_76, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1) | k6_relat_1(k1_relat_1(k6_relat_1(A_1)))!=k6_relat_1(A_1) | k2_relat_1(k6_relat_1(A_1))!=k1_relat_1(k6_relat_1(A_1)) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_74])).
% 1.67/1.10  tff(c_82, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_10, c_68, c_4, c_2, c_2, c_76])).
% 1.67/1.10  tff(c_16, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.67/1.10  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 1.67/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  Inference rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Ref     : 0
% 1.67/1.10  #Sup     : 15
% 1.67/1.10  #Fact    : 0
% 1.67/1.10  #Define  : 0
% 1.67/1.10  #Split   : 0
% 1.67/1.10  #Chain   : 0
% 1.67/1.10  #Close   : 0
% 1.67/1.10  
% 1.67/1.10  Ordering : KBO
% 1.67/1.10  
% 1.67/1.10  Simplification rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Subsume      : 0
% 1.67/1.10  #Demod        : 26
% 1.67/1.10  #Tautology    : 8
% 1.67/1.10  #SimpNegUnit  : 0
% 1.67/1.10  #BackRed      : 1
% 1.67/1.10  
% 1.67/1.10  #Partial instantiations: 0
% 1.67/1.10  #Strategies tried      : 1
% 1.67/1.10  
% 1.67/1.10  Timing (in seconds)
% 1.67/1.10  ----------------------
% 1.67/1.11  Preprocessing        : 0.27
% 1.67/1.11  Parsing              : 0.15
% 1.67/1.11  CNF conversion       : 0.02
% 1.67/1.11  Main loop            : 0.11
% 1.67/1.11  Inferencing          : 0.05
% 1.67/1.11  Reduction            : 0.03
% 1.67/1.11  Demodulation         : 0.03
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.02
% 1.67/1.11  Abstraction          : 0.01
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.40
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
