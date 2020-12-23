%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  85 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_16,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k6_relat_1(k2_relat_1(A_2))) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),k6_relat_1(k1_relat_1(A_21))) = k2_funct_1(A_21)
      | ~ v1_relat_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6])).

tff(c_127,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(k6_relat_1(A_1)),k6_relat_1(A_1)) = k2_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_1)))
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_132,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(k6_relat_1(A_22)),k6_relat_1(A_22)) = k2_funct_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_22))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_18,c_127])).

tff(c_24,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    ! [A_22] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_22))) = k2_funct_1(k6_relat_1(A_22))
      | ~ v2_funct_1(k6_relat_1(A_22))
      | ~ v1_funct_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_22))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_151,plain,(
    ! [A_23] :
      ( k2_funct_1(k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_23))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_18,c_4,c_138])).

tff(c_154,plain,(
    ! [A_23] :
      ( k2_funct_1(k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_157,plain,(
    ! [A_23] : k2_funct_1(k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_154])).

tff(c_28,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.43  
% 1.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.43  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.99/1.43  
% 1.99/1.43  %Foreground sorts:
% 1.99/1.43  
% 1.99/1.43  
% 1.99/1.43  %Background operators:
% 1.99/1.43  
% 1.99/1.43  
% 1.99/1.43  %Foreground operators:
% 1.99/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.99/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.99/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.43  
% 2.20/1.44  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.20/1.44  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.20/1.44  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.20/1.44  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.20/1.44  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.20/1.44  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.20/1.44  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.20/1.44  tff(f_72, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 2.20/1.44  tff(c_16, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.44  tff(c_14, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.44  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.44  tff(c_18, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.44  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.44  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.44  tff(c_85, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.44  tff(c_6, plain, (![A_2]: (k5_relat_1(A_2, k6_relat_1(k2_relat_1(A_2)))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.44  tff(c_115, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), k6_relat_1(k1_relat_1(A_21)))=k2_funct_1(A_21) | ~v1_relat_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_85, c_6])).
% 2.20/1.44  tff(c_127, plain, (![A_1]: (k5_relat_1(k2_funct_1(k6_relat_1(A_1)), k6_relat_1(A_1))=k2_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_1))) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_115])).
% 2.20/1.44  tff(c_132, plain, (![A_22]: (k5_relat_1(k2_funct_1(k6_relat_1(A_22)), k6_relat_1(A_22))=k2_funct_1(k6_relat_1(A_22)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_18, c_127])).
% 2.20/1.44  tff(c_24, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.44  tff(c_138, plain, (![A_22]: (k6_relat_1(k2_relat_1(k6_relat_1(A_22)))=k2_funct_1(k6_relat_1(A_22)) | ~v2_funct_1(k6_relat_1(A_22)) | ~v1_funct_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_22))))), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 2.20/1.44  tff(c_151, plain, (![A_23]: (k2_funct_1(k6_relat_1(A_23))=k6_relat_1(A_23) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_18, c_4, c_138])).
% 2.20/1.44  tff(c_154, plain, (![A_23]: (k2_funct_1(k6_relat_1(A_23))=k6_relat_1(A_23) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(resolution, [status(thm)], [c_10, c_151])).
% 2.20/1.44  tff(c_157, plain, (![A_23]: (k2_funct_1(k6_relat_1(A_23))=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_154])).
% 2.20/1.44  tff(c_28, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.44  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_28])).
% 2.20/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.44  
% 2.20/1.44  Inference rules
% 2.20/1.44  ----------------------
% 2.20/1.44  #Ref     : 0
% 2.20/1.44  #Sup     : 27
% 2.20/1.44  #Fact    : 0
% 2.20/1.44  #Define  : 0
% 2.20/1.44  #Split   : 0
% 2.20/1.44  #Chain   : 0
% 2.20/1.44  #Close   : 0
% 2.20/1.44  
% 2.20/1.44  Ordering : KBO
% 2.20/1.44  
% 2.20/1.44  Simplification rules
% 2.20/1.44  ----------------------
% 2.20/1.44  #Subsume      : 0
% 2.20/1.44  #Demod        : 23
% 2.20/1.44  #Tautology    : 23
% 2.20/1.44  #SimpNegUnit  : 0
% 2.20/1.44  #BackRed      : 2
% 2.20/1.44  
% 2.20/1.44  #Partial instantiations: 0
% 2.20/1.44  #Strategies tried      : 1
% 2.20/1.44  
% 2.20/1.44  Timing (in seconds)
% 2.20/1.44  ----------------------
% 2.20/1.44  Preprocessing        : 0.37
% 2.20/1.44  Parsing              : 0.21
% 2.20/1.44  CNF conversion       : 0.02
% 2.20/1.44  Main loop            : 0.16
% 2.20/1.44  Inferencing          : 0.07
% 2.20/1.44  Reduction            : 0.05
% 2.20/1.44  Demodulation         : 0.04
% 2.20/1.44  BG Simplification    : 0.01
% 2.20/1.44  Subsumption          : 0.03
% 2.20/1.44  Abstraction          : 0.01
% 2.20/1.44  MUC search           : 0.00
% 2.20/1.44  Cooper               : 0.00
% 2.20/1.44  Total                : 0.57
% 2.20/1.44  Index Insertion      : 0.00
% 2.20/1.44  Index Deletion       : 0.00
% 2.20/1.44  Index Matching       : 0.00
% 2.20/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
