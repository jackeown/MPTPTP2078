%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  65 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :   11 (   3 average)
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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

tff(f_58,axiom,(
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

tff(f_61,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_12,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_1] :
      ( k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_54,plain,(
    ! [A_1] : k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_64,plain,(
    ! [A_15,B_16] :
      ( k2_funct_1(A_15) = B_16
      | k6_relat_1(k2_relat_1(A_15)) != k5_relat_1(B_16,A_15)
      | k2_relat_1(B_16) != k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [A_1] :
      ( k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1)
      | k6_relat_1(k2_relat_1(k6_relat_1(A_1))) != k6_relat_1(A_1)
      | k2_relat_1(k6_relat_1(A_1)) != k1_relat_1(k6_relat_1(A_1))
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_72,plain,(
    ! [A_1] : k2_funct_1(k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_12,c_10,c_14,c_4,c_2,c_4,c_66])).

tff(c_18,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:17:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.65/1.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.65/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.65/1.12  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.65/1.12  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.65/1.12  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.65/1.12  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 1.65/1.12  tff(f_61, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.65/1.12  tff(c_12, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.12  tff(c_10, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.12  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.12  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.12  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.12  tff(c_41, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.12  tff(c_50, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 1.65/1.12  tff(c_54, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 1.65/1.12  tff(c_64, plain, (![A_15, B_16]: (k2_funct_1(A_15)=B_16 | k6_relat_1(k2_relat_1(A_15))!=k5_relat_1(B_16, A_15) | k2_relat_1(B_16)!=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.65/1.12  tff(c_66, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1) | k6_relat_1(k2_relat_1(k6_relat_1(A_1)))!=k6_relat_1(A_1) | k2_relat_1(k6_relat_1(A_1))!=k1_relat_1(k6_relat_1(A_1)) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_64])).
% 1.65/1.12  tff(c_72, plain, (![A_1]: (k2_funct_1(k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_12, c_10, c_14, c_4, c_2, c_4, c_66])).
% 1.65/1.12  tff(c_18, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 12
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 20
% 1.65/1.12  #Tautology    : 9
% 1.65/1.12  #SimpNegUnit  : 0
% 1.65/1.12  #BackRed      : 1
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.12  Preprocessing        : 0.26
% 1.65/1.12  Parsing              : 0.15
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.10
% 1.65/1.12  Inferencing          : 0.05
% 1.65/1.12  Reduction            : 0.03
% 1.65/1.12  Demodulation         : 0.02
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.02
% 1.65/1.12  Abstraction          : 0.01
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.38
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
