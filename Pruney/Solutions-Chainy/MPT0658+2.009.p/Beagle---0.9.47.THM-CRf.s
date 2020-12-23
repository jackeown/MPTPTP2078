%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 183 expanded)
%              Number of equality atoms :   32 (  45 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_83,axiom,(
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

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
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

tff(c_8,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [A_18,B_19] :
      ( k2_funct_1(A_18) = B_19
      | k6_relat_1(k2_relat_1(A_18)) != k5_relat_1(B_19,A_18)
      | k2_relat_1(B_19) != k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_88,plain,(
    ! [A_23] :
      ( k2_funct_1(k2_funct_1(A_23)) = A_23
      | k6_relat_1(k2_relat_1(k2_funct_1(A_23))) != k6_relat_1(k1_relat_1(A_23))
      | k1_relat_1(k2_funct_1(A_23)) != k2_relat_1(A_23)
      | ~ v2_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23)
      | ~ v1_funct_1(k2_funct_1(A_23))
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_93,plain,(
    ! [A_24] :
      ( k2_funct_1(k2_funct_1(A_24)) = A_24
      | k1_relat_1(k2_funct_1(A_24)) != k2_relat_1(A_24)
      | ~ v2_funct_1(k2_funct_1(A_24))
      | ~ v1_funct_1(k2_funct_1(A_24))
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_98,plain,(
    ! [A_25] :
      ( k2_funct_1(k2_funct_1(A_25)) = A_25
      | k1_relat_1(k2_funct_1(A_25)) != k2_relat_1(A_25)
      | ~ v1_funct_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_86,c_93])).

tff(c_103,plain,(
    ! [A_26] :
      ( k2_funct_1(k2_funct_1(A_26)) = A_26
      | k1_relat_1(k2_funct_1(A_26)) != k2_relat_1(A_26)
      | ~ v1_funct_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_108,plain,(
    ! [A_27] :
      ( k2_funct_1(k2_funct_1(A_27)) = A_27
      | k1_relat_1(k2_funct_1(A_27)) != k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_18,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_138,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_18])).

tff(c_149,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_138])).

tff(c_154,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_149])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.23/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.34  
% 2.23/1.35  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 2.23/1.35  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.23/1.35  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.23/1.35  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.23/1.35  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 2.23/1.35  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.23/1.35  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.23/1.35  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.23/1.35  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.23/1.35  tff(c_10, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.35  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.35  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.35  tff(c_12, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.35  tff(c_63, plain, (![A_16, B_17]: (v2_funct_1(A_16) | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.35  tff(c_80, plain, (![A_20, B_21]: (v2_funct_1(k2_funct_1(A_20)) | k5_relat_1(k2_funct_1(A_20), B_21)!=k6_relat_1(k2_relat_1(A_20)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(k2_funct_1(A_20)) | ~v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 2.23/1.35  tff(c_86, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 2.23/1.35  tff(c_8, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.35  tff(c_14, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.35  tff(c_71, plain, (![A_18, B_19]: (k2_funct_1(A_18)=B_19 | k6_relat_1(k2_relat_1(A_18))!=k5_relat_1(B_19, A_18) | k2_relat_1(B_19)!=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.35  tff(c_88, plain, (![A_23]: (k2_funct_1(k2_funct_1(A_23))=A_23 | k6_relat_1(k2_relat_1(k2_funct_1(A_23)))!=k6_relat_1(k1_relat_1(A_23)) | k1_relat_1(k2_funct_1(A_23))!=k2_relat_1(A_23) | ~v2_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23) | ~v1_funct_1(k2_funct_1(A_23)) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_14, c_71])).
% 2.23/1.35  tff(c_93, plain, (![A_24]: (k2_funct_1(k2_funct_1(A_24))=A_24 | k1_relat_1(k2_funct_1(A_24))!=k2_relat_1(A_24) | ~v2_funct_1(k2_funct_1(A_24)) | ~v1_funct_1(k2_funct_1(A_24)) | ~v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 2.23/1.35  tff(c_98, plain, (![A_25]: (k2_funct_1(k2_funct_1(A_25))=A_25 | k1_relat_1(k2_funct_1(A_25))!=k2_relat_1(A_25) | ~v1_funct_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_86, c_93])).
% 2.23/1.35  tff(c_103, plain, (![A_26]: (k2_funct_1(k2_funct_1(A_26))=A_26 | k1_relat_1(k2_funct_1(A_26))!=k2_relat_1(A_26) | ~v1_funct_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.23/1.35  tff(c_108, plain, (![A_27]: (k2_funct_1(k2_funct_1(A_27))=A_27 | k1_relat_1(k2_funct_1(A_27))!=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_2, c_103])).
% 2.23/1.35  tff(c_18, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.23/1.35  tff(c_138, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_18])).
% 2.23/1.35  tff(c_149, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_138])).
% 2.23/1.35  tff(c_154, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_149])).
% 2.23/1.35  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_154])).
% 2.23/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  Inference rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Ref     : 0
% 2.23/1.35  #Sup     : 33
% 2.23/1.35  #Fact    : 0
% 2.23/1.35  #Define  : 0
% 2.23/1.35  #Split   : 0
% 2.23/1.35  #Chain   : 0
% 2.23/1.35  #Close   : 0
% 2.23/1.35  
% 2.23/1.35  Ordering : KBO
% 2.23/1.35  
% 2.23/1.35  Simplification rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Subsume      : 8
% 2.23/1.35  #Demod        : 6
% 2.23/1.35  #Tautology    : 18
% 2.23/1.35  #SimpNegUnit  : 0
% 2.23/1.35  #BackRed      : 0
% 2.23/1.35  
% 2.23/1.35  #Partial instantiations: 0
% 2.23/1.35  #Strategies tried      : 1
% 2.23/1.35  
% 2.23/1.35  Timing (in seconds)
% 2.23/1.35  ----------------------
% 2.23/1.35  Preprocessing        : 0.34
% 2.23/1.35  Parsing              : 0.18
% 2.23/1.35  CNF conversion       : 0.02
% 2.23/1.35  Main loop            : 0.17
% 2.23/1.35  Inferencing          : 0.07
% 2.23/1.35  Reduction            : 0.04
% 2.23/1.35  Demodulation         : 0.03
% 2.23/1.35  BG Simplification    : 0.02
% 2.23/1.35  Subsumption          : 0.04
% 2.23/1.35  Abstraction          : 0.01
% 2.23/1.35  MUC search           : 0.00
% 2.23/1.35  Cooper               : 0.00
% 2.23/1.35  Total                : 0.54
% 2.23/1.35  Index Insertion      : 0.00
% 2.23/1.35  Index Deletion       : 0.00
% 2.23/1.35  Index Matching       : 0.00
% 2.23/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
