%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 148 expanded)
%              Number of equality atoms :   28 (  36 expanded)
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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_55,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_82,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_3] :
      ( k1_relat_1(k2_funct_1(A_3)) = k2_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

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

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_15,B_16] :
      ( k2_funct_1(A_15) = B_16
      | k6_relat_1(k2_relat_1(A_15)) != k5_relat_1(B_16,A_15)
      | k2_relat_1(B_16) != k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [A_17] :
      ( k2_funct_1(k2_funct_1(A_17)) = A_17
      | k6_relat_1(k2_relat_1(k2_funct_1(A_17))) != k6_relat_1(k1_relat_1(A_17))
      | k1_relat_1(k2_funct_1(A_17)) != k2_relat_1(A_17)
      | ~ v2_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17)
      | ~ v1_funct_1(k2_funct_1(A_17))
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_82,plain,(
    ! [A_18] :
      ( k2_funct_1(k2_funct_1(A_18)) = A_18
      | k1_relat_1(k2_funct_1(A_18)) != k2_relat_1(A_18)
      | ~ v2_funct_1(k2_funct_1(A_18))
      | ~ v1_funct_1(k2_funct_1(A_18))
      | ~ v1_relat_1(k2_funct_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_87,plain,(
    ! [A_19] :
      ( k2_funct_1(k2_funct_1(A_19)) = A_19
      | k1_relat_1(k2_funct_1(A_19)) != k2_relat_1(A_19)
      | ~ v1_funct_1(k2_funct_1(A_19))
      | ~ v1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_100,plain,(
    ! [A_22] :
      ( k2_funct_1(k2_funct_1(A_22)) = A_22
      | k1_relat_1(k2_funct_1(A_22)) != k2_relat_1(A_22)
      | ~ v1_funct_1(k2_funct_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_105,plain,(
    ! [A_23] :
      ( k2_funct_1(k2_funct_1(A_23)) = A_23
      | k1_relat_1(k2_funct_1(A_23)) != k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_22,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_137,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_148,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_137])).

tff(c_153,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_148])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.24  
% 2.31/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.25  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.31/1.25  
% 2.31/1.25  %Foreground sorts:
% 2.31/1.25  
% 2.31/1.25  
% 2.31/1.25  %Background operators:
% 2.31/1.25  
% 2.31/1.25  
% 2.31/1.25  %Foreground operators:
% 2.31/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.25  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.31/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.25  
% 2.31/1.26  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 2.31/1.26  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.31/1.26  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.31/1.26  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.31/1.26  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.31/1.26  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.31/1.26  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.31/1.26  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.31/1.26  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.31/1.26  tff(c_14, plain, (![A_3]: (k1_relat_1(k2_funct_1(A_3))=k2_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.26  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.26  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.26  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.26  tff(c_12, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.26  tff(c_18, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.26  tff(c_68, plain, (![A_15, B_16]: (k2_funct_1(A_15)=B_16 | k6_relat_1(k2_relat_1(A_15))!=k5_relat_1(B_16, A_15) | k2_relat_1(B_16)!=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.26  tff(c_77, plain, (![A_17]: (k2_funct_1(k2_funct_1(A_17))=A_17 | k6_relat_1(k2_relat_1(k2_funct_1(A_17)))!=k6_relat_1(k1_relat_1(A_17)) | k1_relat_1(k2_funct_1(A_17))!=k2_relat_1(A_17) | ~v2_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17) | ~v1_funct_1(k2_funct_1(A_17)) | ~v1_relat_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_68])).
% 2.31/1.26  tff(c_82, plain, (![A_18]: (k2_funct_1(k2_funct_1(A_18))=A_18 | k1_relat_1(k2_funct_1(A_18))!=k2_relat_1(A_18) | ~v2_funct_1(k2_funct_1(A_18)) | ~v1_funct_1(k2_funct_1(A_18)) | ~v1_relat_1(k2_funct_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_12, c_77])).
% 2.31/1.26  tff(c_87, plain, (![A_19]: (k2_funct_1(k2_funct_1(A_19))=A_19 | k1_relat_1(k2_funct_1(A_19))!=k2_relat_1(A_19) | ~v1_funct_1(k2_funct_1(A_19)) | ~v1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.31/1.26  tff(c_100, plain, (![A_22]: (k2_funct_1(k2_funct_1(A_22))=A_22 | k1_relat_1(k2_funct_1(A_22))!=k2_relat_1(A_22) | ~v1_funct_1(k2_funct_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.31/1.26  tff(c_105, plain, (![A_23]: (k2_funct_1(k2_funct_1(A_23))=A_23 | k1_relat_1(k2_funct_1(A_23))!=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.31/1.26  tff(c_22, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.31/1.26  tff(c_137, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 2.31/1.26  tff(c_148, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_137])).
% 2.31/1.26  tff(c_153, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_148])).
% 2.31/1.26  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_153])).
% 2.31/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.26  
% 2.31/1.26  Inference rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Ref     : 0
% 2.31/1.26  #Sup     : 31
% 2.31/1.26  #Fact    : 0
% 2.31/1.26  #Define  : 0
% 2.31/1.26  #Split   : 0
% 2.31/1.26  #Chain   : 0
% 2.31/1.26  #Close   : 0
% 2.31/1.26  
% 2.31/1.26  Ordering : KBO
% 2.31/1.26  
% 2.31/1.26  Simplification rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Subsume      : 9
% 2.31/1.26  #Demod        : 6
% 2.31/1.26  #Tautology    : 17
% 2.31/1.26  #SimpNegUnit  : 0
% 2.31/1.26  #BackRed      : 0
% 2.31/1.26  
% 2.31/1.26  #Partial instantiations: 0
% 2.31/1.26  #Strategies tried      : 1
% 2.31/1.26  
% 2.31/1.26  Timing (in seconds)
% 2.31/1.26  ----------------------
% 2.31/1.26  Preprocessing        : 0.31
% 2.31/1.26  Parsing              : 0.16
% 2.31/1.26  CNF conversion       : 0.02
% 2.31/1.26  Main loop            : 0.18
% 2.31/1.26  Inferencing          : 0.08
% 2.31/1.26  Reduction            : 0.05
% 2.31/1.26  Demodulation         : 0.03
% 2.31/1.26  BG Simplification    : 0.02
% 2.31/1.26  Subsumption          : 0.04
% 2.31/1.26  Abstraction          : 0.01
% 2.31/1.26  MUC search           : 0.00
% 2.31/1.26  Cooper               : 0.00
% 2.31/1.26  Total                : 0.52
% 2.31/1.26  Index Insertion      : 0.00
% 2.31/1.26  Index Deletion       : 0.00
% 2.31/1.26  Index Matching       : 0.00
% 2.31/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
