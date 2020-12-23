%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 389 expanded)
%              Number of equality atoms :   44 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_135,plain,(
    ! [A_29] :
      ( k4_relat_1(A_29) = k2_funct_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_141,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_138])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_151,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_159,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_151])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_4])).

tff(c_155,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_145])).

tff(c_16,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_16])).

tff(c_168,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_32,c_164])).

tff(c_34,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1(A_19),A_19) = k6_relat_1(k2_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_310,plain,(
    ! [A_39,B_40,C_41] :
      ( k5_relat_1(k5_relat_1(A_39,B_40),C_41) = k5_relat_1(A_39,k5_relat_1(B_40,C_41))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1722,plain,(
    ! [A_88,C_89] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_88)),C_89) = k5_relat_1(k2_funct_1(A_88),k5_relat_1(A_88,C_89))
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1(A_88)
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_310])).

tff(c_1894,plain,(
    ! [C_89] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_89) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_89))
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1722])).

tff(c_1940,plain,(
    ! [C_90] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_90) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_90))
      | ~ v1_relat_1(C_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_159,c_44,c_1894])).

tff(c_454,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k2_relat_1(B_44),k1_relat_1(A_45))
      | k1_relat_1(k5_relat_1(B_44,A_45)) != k1_relat_1(B_44)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_481,plain,(
    ! [A_45] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_45))
      | k1_relat_1(k5_relat_1('#skF_1',A_45)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_454])).

tff(c_490,plain,(
    ! [A_46] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_46))
      | k1_relat_1(k5_relat_1('#skF_1',A_46)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_481])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = B_12
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_496,plain,(
    ! [A_46] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_46)),'#skF_2') = '#skF_2'
      | ~ v1_relat_1('#skF_2')
      | k1_relat_1(k5_relat_1('#skF_1',A_46)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_490,c_14])).

tff(c_514,plain,(
    ! [A_46] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_46)),'#skF_2') = '#skF_2'
      | k1_relat_1(k5_relat_1('#skF_1',A_46)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_496])).

tff(c_1965,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_514])).

tff(c_2050,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_38,c_70,c_168,c_1965])).

tff(c_2052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.83  
% 4.26/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.84  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.26/1.84  
% 4.26/1.84  %Foreground sorts:
% 4.26/1.84  
% 4.26/1.84  
% 4.26/1.84  %Background operators:
% 4.26/1.84  
% 4.26/1.84  
% 4.26/1.84  %Foreground operators:
% 4.26/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.26/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.26/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.84  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.26/1.84  
% 4.26/1.85  tff(f_116, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.26/1.85  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.26/1.85  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 4.26/1.85  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.26/1.85  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.26/1.85  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 4.26/1.85  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.26/1.85  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 4.26/1.85  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 4.26/1.85  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 4.26/1.85  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_32, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.26/1.85  tff(c_70, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_10])).
% 4.26/1.85  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_135, plain, (![A_29]: (k4_relat_1(A_29)=k2_funct_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.26/1.85  tff(c_138, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_135])).
% 4.26/1.85  tff(c_141, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_138])).
% 4.26/1.85  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.85  tff(c_151, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 4.26/1.85  tff(c_159, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_151])).
% 4.26/1.85  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.85  tff(c_145, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_4])).
% 4.26/1.85  tff(c_155, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_145])).
% 4.26/1.85  tff(c_16, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.26/1.85  tff(c_164, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_16])).
% 4.26/1.85  tff(c_168, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_32, c_164])).
% 4.26/1.85  tff(c_34, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.26/1.85  tff(c_26, plain, (![A_19]: (k5_relat_1(k2_funct_1(A_19), A_19)=k6_relat_1(k2_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.26/1.85  tff(c_310, plain, (![A_39, B_40, C_41]: (k5_relat_1(k5_relat_1(A_39, B_40), C_41)=k5_relat_1(A_39, k5_relat_1(B_40, C_41)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.26/1.85  tff(c_1722, plain, (![A_88, C_89]: (k5_relat_1(k6_relat_1(k2_relat_1(A_88)), C_89)=k5_relat_1(k2_funct_1(A_88), k5_relat_1(A_88, C_89)) | ~v1_relat_1(C_89) | ~v1_relat_1(A_88) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_26, c_310])).
% 4.26/1.85  tff(c_1894, plain, (![C_89]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_89)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_89)) | ~v1_relat_1(C_89) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1722])).
% 4.26/1.85  tff(c_1940, plain, (![C_90]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_90)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_90)) | ~v1_relat_1(C_90))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_159, c_44, c_1894])).
% 4.26/1.85  tff(c_454, plain, (![B_44, A_45]: (r1_tarski(k2_relat_1(B_44), k1_relat_1(A_45)) | k1_relat_1(k5_relat_1(B_44, A_45))!=k1_relat_1(B_44) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.26/1.85  tff(c_481, plain, (![A_45]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_45)) | k1_relat_1(k5_relat_1('#skF_1', A_45))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_34, c_454])).
% 4.26/1.85  tff(c_490, plain, (![A_46]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_46)) | k1_relat_1(k5_relat_1('#skF_1', A_46))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_481])).
% 4.26/1.85  tff(c_14, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=B_12 | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.26/1.85  tff(c_496, plain, (![A_46]: (k5_relat_1(k6_relat_1(k1_relat_1(A_46)), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2') | k1_relat_1(k5_relat_1('#skF_1', A_46))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_490, c_14])).
% 4.26/1.85  tff(c_514, plain, (![A_46]: (k5_relat_1(k6_relat_1(k1_relat_1(A_46)), '#skF_2')='#skF_2' | k1_relat_1(k5_relat_1('#skF_1', A_46))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_496])).
% 4.26/1.85  tff(c_1965, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1940, c_514])).
% 4.26/1.85  tff(c_2050, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_38, c_70, c_168, c_1965])).
% 4.26/1.85  tff(c_2052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2050])).
% 4.26/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.85  
% 4.26/1.85  Inference rules
% 4.26/1.85  ----------------------
% 4.26/1.85  #Ref     : 0
% 4.26/1.85  #Sup     : 459
% 4.26/1.85  #Fact    : 0
% 4.26/1.85  #Define  : 0
% 4.26/1.85  #Split   : 15
% 4.26/1.85  #Chain   : 0
% 4.26/1.85  #Close   : 0
% 4.26/1.85  
% 4.26/1.85  Ordering : KBO
% 4.26/1.85  
% 4.26/1.85  Simplification rules
% 4.26/1.85  ----------------------
% 4.26/1.85  #Subsume      : 110
% 4.26/1.85  #Demod        : 573
% 4.26/1.85  #Tautology    : 138
% 4.26/1.85  #SimpNegUnit  : 7
% 4.26/1.85  #BackRed      : 0
% 4.26/1.85  
% 4.26/1.85  #Partial instantiations: 0
% 4.26/1.85  #Strategies tried      : 1
% 4.26/1.85  
% 4.26/1.85  Timing (in seconds)
% 4.26/1.85  ----------------------
% 4.26/1.85  Preprocessing        : 0.32
% 4.26/1.85  Parsing              : 0.17
% 4.26/1.85  CNF conversion       : 0.02
% 4.26/1.85  Main loop            : 0.70
% 4.26/1.85  Inferencing          : 0.25
% 4.26/1.85  Reduction            : 0.26
% 4.26/1.85  Demodulation         : 0.19
% 4.26/1.85  BG Simplification    : 0.03
% 4.26/1.85  Subsumption          : 0.13
% 4.26/1.85  Abstraction          : 0.04
% 4.26/1.85  MUC search           : 0.00
% 4.26/1.85  Cooper               : 0.00
% 4.26/1.85  Total                : 1.05
% 4.26/1.85  Index Insertion      : 0.00
% 4.26/1.85  Index Deletion       : 0.00
% 4.26/1.85  Index Matching       : 0.00
% 4.26/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
