%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 191 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 633 expanded)
%              Number of equality atoms :   34 ( 229 expanded)
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
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

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

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_84,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_90,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_87])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4])).

tff(c_112,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24,c_106])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_125,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_128,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_128])).

tff(c_134,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,(
    ! [A_23,B_24,C_25] :
      ( k5_relat_1(k5_relat_1(A_23,B_24),C_25) = k5_relat_1(A_23,k5_relat_1(B_24,C_25))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_502,plain,(
    ! [A_32,C_33] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_32)),C_33) = k5_relat_1(k2_funct_1(A_32),k5_relat_1(A_32,C_33))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_175])).

tff(c_600,plain,(
    ! [C_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_33) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_33))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_502])).

tff(c_611,plain,(
    ! [C_34] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_34) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_34))
      | ~ v1_relat_1(C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_134,c_34,c_600])).

tff(c_649,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_8])).

tff(c_690,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_649])).

tff(c_22,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_133,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_641,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_133])).

tff(c_688,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_641])).

tff(c_741,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_688])).

tff(c_751,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_690,c_22,c_741])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.59  
% 2.86/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.59  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.86/1.59  
% 2.86/1.59  %Foreground sorts:
% 2.86/1.59  
% 2.86/1.59  
% 2.86/1.59  %Background operators:
% 2.86/1.59  
% 2.86/1.59  
% 2.86/1.59  %Foreground operators:
% 2.86/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.86/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.86/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.59  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.86/1.59  
% 2.86/1.61  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.86/1.61  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.86/1.61  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.86/1.61  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.86/1.61  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.86/1.61  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.86/1.61  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.86/1.61  tff(c_20, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.61  tff(c_24, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_84, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.86/1.61  tff(c_87, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_84])).
% 2.86/1.61  tff(c_90, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_87])).
% 2.86/1.61  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.61  tff(c_106, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_4])).
% 2.86/1.61  tff(c_112, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24, c_106])).
% 2.86/1.61  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.61  tff(c_121, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 2.86/1.61  tff(c_125, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_121])).
% 2.86/1.61  tff(c_128, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_125])).
% 2.86/1.61  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_128])).
% 2.86/1.61  tff(c_134, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_121])).
% 2.86/1.61  tff(c_16, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.61  tff(c_175, plain, (![A_23, B_24, C_25]: (k5_relat_1(k5_relat_1(A_23, B_24), C_25)=k5_relat_1(A_23, k5_relat_1(B_24, C_25)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.61  tff(c_502, plain, (![A_32, C_33]: (k5_relat_1(k6_relat_1(k2_relat_1(A_32)), C_33)=k5_relat_1(k2_funct_1(A_32), k5_relat_1(A_32, C_33)) | ~v1_relat_1(C_33) | ~v1_relat_1(A_32) | ~v1_relat_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_16, c_175])).
% 2.86/1.61  tff(c_600, plain, (![C_33]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_33)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_33)) | ~v1_relat_1(C_33) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_502])).
% 2.86/1.61  tff(c_611, plain, (![C_34]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_34)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_34)) | ~v1_relat_1(C_34))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_134, c_34, c_600])).
% 2.86/1.61  tff(c_649, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_611, c_8])).
% 2.86/1.61  tff(c_690, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_649])).
% 2.86/1.61  tff(c_22, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.61  tff(c_18, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.61  tff(c_133, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_121])).
% 2.86/1.61  tff(c_641, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_611, c_133])).
% 2.86/1.61  tff(c_688, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_641])).
% 2.86/1.61  tff(c_741, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_688])).
% 2.86/1.61  tff(c_751, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_690, c_22, c_741])).
% 2.86/1.61  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_751])).
% 2.86/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.61  
% 2.86/1.61  Inference rules
% 2.86/1.61  ----------------------
% 2.86/1.61  #Ref     : 0
% 2.86/1.61  #Sup     : 181
% 2.86/1.61  #Fact    : 0
% 2.86/1.61  #Define  : 0
% 2.86/1.61  #Split   : 6
% 2.86/1.61  #Chain   : 0
% 2.86/1.61  #Close   : 0
% 2.86/1.61  
% 2.86/1.61  Ordering : KBO
% 2.86/1.61  
% 2.86/1.61  Simplification rules
% 2.86/1.61  ----------------------
% 2.86/1.61  #Subsume      : 29
% 2.86/1.61  #Demod        : 149
% 2.86/1.61  #Tautology    : 56
% 2.86/1.61  #SimpNegUnit  : 1
% 2.86/1.61  #BackRed      : 0
% 2.86/1.61  
% 2.86/1.61  #Partial instantiations: 0
% 2.86/1.61  #Strategies tried      : 1
% 2.86/1.61  
% 2.86/1.61  Timing (in seconds)
% 2.86/1.61  ----------------------
% 2.86/1.61  Preprocessing        : 0.40
% 2.86/1.61  Parsing              : 0.24
% 2.86/1.61  CNF conversion       : 0.02
% 2.86/1.61  Main loop            : 0.36
% 2.86/1.61  Inferencing          : 0.14
% 2.86/1.61  Reduction            : 0.12
% 2.86/1.61  Demodulation         : 0.08
% 2.86/1.61  BG Simplification    : 0.02
% 2.86/1.61  Subsumption          : 0.06
% 2.86/1.61  Abstraction          : 0.02
% 2.86/1.61  MUC search           : 0.00
% 2.86/1.61  Cooper               : 0.00
% 2.86/1.61  Total                : 0.79
% 2.86/1.61  Index Insertion      : 0.00
% 2.86/1.61  Index Deletion       : 0.00
% 2.86/1.61  Index Matching       : 0.00
% 2.86/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
