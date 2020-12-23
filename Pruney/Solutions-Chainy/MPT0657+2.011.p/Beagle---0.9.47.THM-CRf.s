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
% DateTime   : Thu Dec  3 10:04:05 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 178 expanded)
%              Number of leaves         :   21 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 570 expanded)
%              Number of equality atoms :   38 ( 204 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_20,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_84,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_78])).

tff(c_18,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_99,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_96])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_2])).

tff(c_110,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_103])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8])).

tff(c_125,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_128,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_128])).

tff(c_134,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_133,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_22,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_157,plain,(
    ! [A_22,B_23,C_24] :
      ( k5_relat_1(k5_relat_1(A_22,B_23),C_24) = k5_relat_1(A_22,k5_relat_1(B_23,C_24))
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_330,plain,(
    ! [A_29,C_30] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_29)),C_30) = k5_relat_1(k2_funct_1(A_29),k5_relat_1(A_29,C_30))
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_157])).

tff(c_414,plain,(
    ! [C_30] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_30)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_330])).

tff(c_428,plain,(
    ! [C_31] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_31)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_134,c_34,c_414])).

tff(c_448,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_428])).

tff(c_465,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_134,c_133,c_448])).

tff(c_6,plain,(
    ! [A_2,B_6,C_8] :
      ( k5_relat_1(k5_relat_1(A_2,B_6),C_8) = k5_relat_1(A_2,k5_relat_1(B_6,C_8))
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_477,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_6])).

tff(c_488,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_134,c_477])).

tff(c_499,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_488])).

tff(c_505,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_84,c_499])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.58/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.58/1.35  
% 2.58/1.36  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.58/1.36  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.58/1.36  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.58/1.36  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.58/1.36  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.58/1.36  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.58/1.36  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.58/1.36  tff(c_20, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_24, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_63, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.36  tff(c_78, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_63])).
% 2.58/1.36  tff(c_84, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_78])).
% 2.58/1.36  tff(c_18, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.36  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.36  tff(c_93, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.36  tff(c_96, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_93])).
% 2.58/1.36  tff(c_99, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_96])).
% 2.58/1.36  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.36  tff(c_103, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_2])).
% 2.58/1.36  tff(c_110, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_103])).
% 2.58/1.36  tff(c_8, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.36  tff(c_117, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_8])).
% 2.58/1.36  tff(c_125, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_117])).
% 2.58/1.36  tff(c_128, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_125])).
% 2.58/1.36  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_128])).
% 2.58/1.36  tff(c_134, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_117])).
% 2.58/1.36  tff(c_133, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_117])).
% 2.58/1.36  tff(c_22, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.36  tff(c_16, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.36  tff(c_157, plain, (![A_22, B_23, C_24]: (k5_relat_1(k5_relat_1(A_22, B_23), C_24)=k5_relat_1(A_22, k5_relat_1(B_23, C_24)) | ~v1_relat_1(C_24) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.36  tff(c_330, plain, (![A_29, C_30]: (k5_relat_1(k6_relat_1(k2_relat_1(A_29)), C_30)=k5_relat_1(k2_funct_1(A_29), k5_relat_1(A_29, C_30)) | ~v1_relat_1(C_30) | ~v1_relat_1(A_29) | ~v1_relat_1(k2_funct_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_16, c_157])).
% 2.58/1.36  tff(c_414, plain, (![C_30]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_30))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_30) | ~v1_relat_1(C_30) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_330])).
% 2.58/1.36  tff(c_428, plain, (![C_31]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_31))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_31) | ~v1_relat_1(C_31))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_134, c_34, c_414])).
% 2.58/1.36  tff(c_448, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_428])).
% 2.58/1.36  tff(c_465, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_134, c_133, c_448])).
% 2.58/1.36  tff(c_6, plain, (![A_2, B_6, C_8]: (k5_relat_1(k5_relat_1(A_2, B_6), C_8)=k5_relat_1(A_2, k5_relat_1(B_6, C_8)) | ~v1_relat_1(C_8) | ~v1_relat_1(B_6) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.36  tff(c_477, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_465, c_6])).
% 2.58/1.36  tff(c_488, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_134, c_477])).
% 2.58/1.36  tff(c_499, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_488])).
% 2.58/1.36  tff(c_505, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_84, c_499])).
% 2.58/1.36  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_505])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 0
% 2.58/1.36  #Sup     : 120
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 5
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 13
% 2.58/1.36  #Demod        : 82
% 2.58/1.36  #Tautology    : 45
% 2.58/1.36  #SimpNegUnit  : 1
% 2.58/1.36  #BackRed      : 0
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.37  Preprocessing        : 0.29
% 2.58/1.37  Parsing              : 0.16
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.30
% 2.58/1.37  Inferencing          : 0.12
% 2.58/1.37  Reduction            : 0.09
% 2.58/1.37  Demodulation         : 0.07
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.05
% 2.58/1.37  Abstraction          : 0.02
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.63
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
