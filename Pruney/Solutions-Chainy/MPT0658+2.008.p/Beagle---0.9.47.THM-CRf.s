%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 167 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :   13 (   5 average)
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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

tff(f_83,axiom,(
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

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

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

tff(c_12,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [A_16,B_17] :
      ( v2_funct_1(A_16)
      | k6_relat_1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [A_20,B_21] :
      ( v2_funct_1(k2_funct_1(A_20))
      | k5_relat_1(k2_funct_1(A_20),B_21) != k6_relat_1(k2_relat_1(A_20))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(k2_funct_1(A_20))
      | ~ v1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_86,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_71,plain,(
    ! [A_18,B_19] :
      ( k2_funct_1(A_18) = B_19
      | k6_relat_1(k1_relat_1(A_18)) != k5_relat_1(A_18,B_19)
      | k2_relat_1(A_18) != k1_relat_1(B_19)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_88,plain,(
    ! [A_23] :
      ( k2_funct_1(k2_funct_1(A_23)) = A_23
      | k6_relat_1(k1_relat_1(k2_funct_1(A_23))) != k6_relat_1(k2_relat_1(A_23))
      | k2_relat_1(k2_funct_1(A_23)) != k1_relat_1(A_23)
      | ~ v2_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23)
      | ~ v1_funct_1(k2_funct_1(A_23))
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_93,plain,(
    ! [A_24] :
      ( k2_funct_1(k2_funct_1(A_24)) = A_24
      | k2_relat_1(k2_funct_1(A_24)) != k1_relat_1(A_24)
      | ~ v2_funct_1(k2_funct_1(A_24))
      | ~ v1_funct_1(k2_funct_1(A_24))
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_98,plain,(
    ! [A_25] :
      ( k2_funct_1(k2_funct_1(A_25)) = A_25
      | k2_relat_1(k2_funct_1(A_25)) != k1_relat_1(A_25)
      | ~ v1_funct_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_86,c_93])).

tff(c_103,plain,(
    ! [A_26] :
      ( k2_funct_1(k2_funct_1(A_26)) = A_26
      | k2_relat_1(k2_funct_1(A_26)) != k1_relat_1(A_26)
      | ~ v1_funct_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_108,plain,(
    ! [A_27] :
      ( k2_funct_1(k2_funct_1(A_27)) = A_27
      | k2_relat_1(k2_funct_1(A_27)) != k1_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_113,plain,(
    ! [A_28] :
      ( k2_funct_1(k2_funct_1(A_28)) = A_28
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_18,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_143,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.09/1.29  
% 2.09/1.29  %Foreground sorts:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Background operators:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Foreground operators:
% 2.09/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.09/1.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.29  
% 2.09/1.31  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 2.09/1.31  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.09/1.31  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.09/1.31  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.09/1.31  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 2.09/1.31  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 2.09/1.31  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.09/1.31  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.09/1.31  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.09/1.31  tff(c_8, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.31  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_12, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.31  tff(c_10, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.31  tff(c_63, plain, (![A_16, B_17]: (v2_funct_1(A_16) | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.31  tff(c_80, plain, (![A_20, B_21]: (v2_funct_1(k2_funct_1(A_20)) | k5_relat_1(k2_funct_1(A_20), B_21)!=k6_relat_1(k2_relat_1(A_20)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(k2_funct_1(A_20)) | ~v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 2.09/1.31  tff(c_86, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 2.09/1.31  tff(c_71, plain, (![A_18, B_19]: (k2_funct_1(A_18)=B_19 | k6_relat_1(k1_relat_1(A_18))!=k5_relat_1(A_18, B_19) | k2_relat_1(A_18)!=k1_relat_1(B_19) | ~v2_funct_1(A_18) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.09/1.31  tff(c_88, plain, (![A_23]: (k2_funct_1(k2_funct_1(A_23))=A_23 | k6_relat_1(k1_relat_1(k2_funct_1(A_23)))!=k6_relat_1(k2_relat_1(A_23)) | k2_relat_1(k2_funct_1(A_23))!=k1_relat_1(A_23) | ~v2_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23) | ~v1_funct_1(k2_funct_1(A_23)) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 2.09/1.31  tff(c_93, plain, (![A_24]: (k2_funct_1(k2_funct_1(A_24))=A_24 | k2_relat_1(k2_funct_1(A_24))!=k1_relat_1(A_24) | ~v2_funct_1(k2_funct_1(A_24)) | ~v1_funct_1(k2_funct_1(A_24)) | ~v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_10, c_88])).
% 2.09/1.31  tff(c_98, plain, (![A_25]: (k2_funct_1(k2_funct_1(A_25))=A_25 | k2_relat_1(k2_funct_1(A_25))!=k1_relat_1(A_25) | ~v1_funct_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_86, c_93])).
% 2.09/1.31  tff(c_103, plain, (![A_26]: (k2_funct_1(k2_funct_1(A_26))=A_26 | k2_relat_1(k2_funct_1(A_26))!=k1_relat_1(A_26) | ~v1_funct_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.09/1.31  tff(c_108, plain, (![A_27]: (k2_funct_1(k2_funct_1(A_27))=A_27 | k2_relat_1(k2_funct_1(A_27))!=k1_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_2, c_103])).
% 2.09/1.31  tff(c_113, plain, (![A_28]: (k2_funct_1(k2_funct_1(A_28))=A_28 | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_108])).
% 2.09/1.31  tff(c_18, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.09/1.31  tff(c_143, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_18])).
% 2.09/1.31  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_143])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 33
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 0
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 9
% 2.09/1.31  #Demod        : 3
% 2.09/1.31  #Tautology    : 16
% 2.09/1.31  #SimpNegUnit  : 0
% 2.09/1.31  #BackRed      : 0
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.31  Preprocessing        : 0.32
% 2.09/1.31  Parsing              : 0.18
% 2.09/1.31  CNF conversion       : 0.02
% 2.09/1.31  Main loop            : 0.17
% 2.09/1.31  Inferencing          : 0.07
% 2.09/1.31  Reduction            : 0.05
% 2.09/1.31  Demodulation         : 0.03
% 2.09/1.31  BG Simplification    : 0.01
% 2.09/1.31  Subsumption          : 0.04
% 2.09/1.31  Abstraction          : 0.01
% 2.09/1.31  MUC search           : 0.00
% 2.09/1.31  Cooper               : 0.00
% 2.09/1.31  Total                : 0.52
% 2.09/1.31  Index Insertion      : 0.00
% 2.09/1.31  Index Deletion       : 0.00
% 2.09/1.31  Index Matching       : 0.00
% 2.09/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
