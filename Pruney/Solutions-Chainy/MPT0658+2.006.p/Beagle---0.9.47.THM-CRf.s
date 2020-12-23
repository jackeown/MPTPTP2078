%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 132 expanded)
%              Number of equality atoms :   27 (  32 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_55,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_82,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
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

tff(c_14,plain,(
    ! [A_3] :
      ( k1_relat_1(k2_funct_1(A_3)) = k2_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_15,B_16] :
      ( k2_funct_1(A_15) = B_16
      | k6_relat_1(k1_relat_1(A_15)) != k5_relat_1(A_15,B_16)
      | k2_relat_1(A_15) != k1_relat_1(B_16)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [A_17] :
      ( k2_funct_1(k2_funct_1(A_17)) = A_17
      | k6_relat_1(k1_relat_1(k2_funct_1(A_17))) != k6_relat_1(k2_relat_1(A_17))
      | k2_relat_1(k2_funct_1(A_17)) != k1_relat_1(A_17)
      | ~ v2_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17)
      | ~ v1_funct_1(k2_funct_1(A_17))
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_82,plain,(
    ! [A_18] :
      ( k2_funct_1(k2_funct_1(A_18)) = A_18
      | k2_relat_1(k2_funct_1(A_18)) != k1_relat_1(A_18)
      | ~ v2_funct_1(k2_funct_1(A_18))
      | ~ v1_funct_1(k2_funct_1(A_18))
      | ~ v1_relat_1(k2_funct_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_87,plain,(
    ! [A_19] :
      ( k2_funct_1(k2_funct_1(A_19)) = A_19
      | k2_relat_1(k2_funct_1(A_19)) != k1_relat_1(A_19)
      | ~ v1_funct_1(k2_funct_1(A_19))
      | ~ v1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_100,plain,(
    ! [A_22] :
      ( k2_funct_1(k2_funct_1(A_22)) = A_22
      | k2_relat_1(k2_funct_1(A_22)) != k1_relat_1(A_22)
      | ~ v1_funct_1(k2_funct_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_105,plain,(
    ! [A_23] :
      ( k2_funct_1(k2_funct_1(A_23)) = A_23
      | k2_relat_1(k2_funct_1(A_23)) != k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_110,plain,(
    ! [A_24] :
      ( k2_funct_1(k2_funct_1(A_24)) = A_24
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_105])).

tff(c_22,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_142,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_22])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.22  
% 2.07/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.22  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.07/1.22  
% 2.07/1.22  %Foreground sorts:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Background operators:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Foreground operators:
% 2.07/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.07/1.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.07/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.22  
% 2.24/1.23  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 2.24/1.23  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.24/1.23  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.24/1.23  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.24/1.23  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.24/1.23  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 2.24/1.23  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.23  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.23  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.23  tff(c_12, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.23  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.23  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.23  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.23  tff(c_14, plain, (![A_3]: (k1_relat_1(k2_funct_1(A_3))=k2_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.23  tff(c_16, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.23  tff(c_68, plain, (![A_15, B_16]: (k2_funct_1(A_15)=B_16 | k6_relat_1(k1_relat_1(A_15))!=k5_relat_1(A_15, B_16) | k2_relat_1(A_15)!=k1_relat_1(B_16) | ~v2_funct_1(A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.23  tff(c_77, plain, (![A_17]: (k2_funct_1(k2_funct_1(A_17))=A_17 | k6_relat_1(k1_relat_1(k2_funct_1(A_17)))!=k6_relat_1(k2_relat_1(A_17)) | k2_relat_1(k2_funct_1(A_17))!=k1_relat_1(A_17) | ~v2_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17) | ~v1_funct_1(k2_funct_1(A_17)) | ~v1_relat_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_68])).
% 2.24/1.23  tff(c_82, plain, (![A_18]: (k2_funct_1(k2_funct_1(A_18))=A_18 | k2_relat_1(k2_funct_1(A_18))!=k1_relat_1(A_18) | ~v2_funct_1(k2_funct_1(A_18)) | ~v1_funct_1(k2_funct_1(A_18)) | ~v1_relat_1(k2_funct_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_14, c_77])).
% 2.24/1.23  tff(c_87, plain, (![A_19]: (k2_funct_1(k2_funct_1(A_19))=A_19 | k2_relat_1(k2_funct_1(A_19))!=k1_relat_1(A_19) | ~v1_funct_1(k2_funct_1(A_19)) | ~v1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.24/1.23  tff(c_100, plain, (![A_22]: (k2_funct_1(k2_funct_1(A_22))=A_22 | k2_relat_1(k2_funct_1(A_22))!=k1_relat_1(A_22) | ~v1_funct_1(k2_funct_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.24/1.23  tff(c_105, plain, (![A_23]: (k2_funct_1(k2_funct_1(A_23))=A_23 | k2_relat_1(k2_funct_1(A_23))!=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.24/1.23  tff(c_110, plain, (![A_24]: (k2_funct_1(k2_funct_1(A_24))=A_24 | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_105])).
% 2.24/1.23  tff(c_22, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.23  tff(c_142, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_110, c_22])).
% 2.24/1.23  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_142])).
% 2.24/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.23  
% 2.24/1.23  Inference rules
% 2.24/1.23  ----------------------
% 2.24/1.23  #Ref     : 0
% 2.24/1.23  #Sup     : 31
% 2.24/1.23  #Fact    : 0
% 2.24/1.23  #Define  : 0
% 2.24/1.23  #Split   : 0
% 2.24/1.23  #Chain   : 0
% 2.24/1.23  #Close   : 0
% 2.24/1.23  
% 2.24/1.23  Ordering : KBO
% 2.24/1.23  
% 2.24/1.23  Simplification rules
% 2.24/1.23  ----------------------
% 2.24/1.23  #Subsume      : 10
% 2.24/1.23  #Demod        : 3
% 2.24/1.23  #Tautology    : 15
% 2.24/1.23  #SimpNegUnit  : 0
% 2.24/1.23  #BackRed      : 0
% 2.24/1.23  
% 2.24/1.23  #Partial instantiations: 0
% 2.24/1.23  #Strategies tried      : 1
% 2.24/1.23  
% 2.24/1.23  Timing (in seconds)
% 2.24/1.23  ----------------------
% 2.24/1.24  Preprocessing        : 0.31
% 2.24/1.24  Parsing              : 0.16
% 2.24/1.24  CNF conversion       : 0.02
% 2.24/1.24  Main loop            : 0.18
% 2.24/1.24  Inferencing          : 0.07
% 2.24/1.24  Reduction            : 0.04
% 2.24/1.24  Demodulation         : 0.03
% 2.24/1.24  BG Simplification    : 0.02
% 2.24/1.24  Subsumption          : 0.04
% 2.24/1.24  Abstraction          : 0.01
% 2.24/1.24  MUC search           : 0.00
% 2.24/1.24  Cooper               : 0.00
% 2.24/1.24  Total                : 0.51
% 2.24/1.24  Index Insertion      : 0.00
% 2.24/1.24  Index Deletion       : 0.00
% 2.24/1.24  Index Matching       : 0.00
% 2.24/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
