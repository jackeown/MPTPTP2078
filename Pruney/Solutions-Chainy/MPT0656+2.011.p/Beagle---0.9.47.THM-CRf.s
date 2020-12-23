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
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 159 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 537 expanded)
%              Number of equality atoms :   34 ( 175 expanded)
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

tff(f_85,negated_conjecture,(
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

tff(f_57,axiom,(
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

tff(f_67,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_87,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_84])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_105,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97])).

tff(c_22,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,(
    ! [A_22,B_23,C_24] :
      ( k5_relat_1(k5_relat_1(A_22,B_23),C_24) = k5_relat_1(A_22,k5_relat_1(B_23,C_24))
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_580,plain,(
    ! [A_31,C_32] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_31)),C_32) = k5_relat_1(k2_funct_1(A_31),k5_relat_1(A_31,C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(A_31)
      | ~ v1_relat_1(k2_funct_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_179])).

tff(c_684,plain,(
    ! [C_32] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_32) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_580])).

tff(c_699,plain,(
    ! [C_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_33) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_33))
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_105,c_32,c_684])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_10)),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_740,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_10])).

tff(c_786,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_740])).

tff(c_20,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_101,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_91])).

tff(c_119,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_123,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_119])).

tff(c_736,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_123])).

tff(c_784,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_736])).

tff(c_839,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_784])).

tff(c_849,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_786,c_20,c_839])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.48  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.16/1.48  
% 3.16/1.48  %Foreground sorts:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Background operators:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Foreground operators:
% 3.16/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.16/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.16/1.48  
% 3.16/1.49  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.16/1.49  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.16/1.49  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.16/1.49  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.16/1.49  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.16/1.49  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.16/1.49  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.16/1.49  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_81, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.49  tff(c_84, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_81])).
% 3.16/1.49  tff(c_87, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_84])).
% 3.16/1.49  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.49  tff(c_97, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 3.16/1.49  tff(c_105, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_97])).
% 3.16/1.49  tff(c_22, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_14, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.49  tff(c_179, plain, (![A_22, B_23, C_24]: (k5_relat_1(k5_relat_1(A_22, B_23), C_24)=k5_relat_1(A_22, k5_relat_1(B_23, C_24)) | ~v1_relat_1(C_24) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.49  tff(c_580, plain, (![A_31, C_32]: (k5_relat_1(k6_relat_1(k2_relat_1(A_31)), C_32)=k5_relat_1(k2_funct_1(A_31), k5_relat_1(A_31, C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(A_31) | ~v1_relat_1(k2_funct_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_179])).
% 3.16/1.49  tff(c_684, plain, (![C_32]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_32)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_580])).
% 3.16/1.49  tff(c_699, plain, (![C_33]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_33)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_33)) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_105, c_32, c_684])).
% 3.16/1.49  tff(c_10, plain, (![A_10]: (k5_relat_1(k6_relat_1(k1_relat_1(A_10)), A_10)=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.49  tff(c_740, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_699, c_10])).
% 3.16/1.49  tff(c_786, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_740])).
% 3.16/1.49  tff(c_20, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.49  tff(c_16, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.49  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.49  tff(c_91, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 3.16/1.49  tff(c_101, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_91])).
% 3.16/1.49  tff(c_119, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 3.16/1.49  tff(c_123, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_119])).
% 3.16/1.49  tff(c_736, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_699, c_123])).
% 3.16/1.49  tff(c_784, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_736])).
% 3.16/1.49  tff(c_839, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_784])).
% 3.16/1.49  tff(c_849, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_786, c_20, c_839])).
% 3.16/1.49  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_849])).
% 3.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  Inference rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Ref     : 0
% 3.16/1.49  #Sup     : 203
% 3.16/1.49  #Fact    : 0
% 3.16/1.49  #Define  : 0
% 3.16/1.49  #Split   : 7
% 3.16/1.49  #Chain   : 0
% 3.16/1.49  #Close   : 0
% 3.16/1.49  
% 3.16/1.49  Ordering : KBO
% 3.16/1.49  
% 3.16/1.49  Simplification rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Subsume      : 36
% 3.16/1.49  #Demod        : 189
% 3.16/1.49  #Tautology    : 65
% 3.16/1.49  #SimpNegUnit  : 1
% 3.16/1.49  #BackRed      : 0
% 3.16/1.49  
% 3.16/1.49  #Partial instantiations: 0
% 3.16/1.49  #Strategies tried      : 1
% 3.16/1.49  
% 3.16/1.49  Timing (in seconds)
% 3.16/1.49  ----------------------
% 3.29/1.49  Preprocessing        : 0.30
% 3.29/1.49  Parsing              : 0.16
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.43
% 3.29/1.50  Inferencing          : 0.17
% 3.29/1.50  Reduction            : 0.14
% 3.29/1.50  Demodulation         : 0.11
% 3.29/1.50  BG Simplification    : 0.03
% 3.29/1.50  Subsumption          : 0.07
% 3.29/1.50  Abstraction          : 0.03
% 3.29/1.50  MUC search           : 0.00
% 3.29/1.50  Cooper               : 0.00
% 3.29/1.50  Total                : 0.76
% 3.29/1.50  Index Insertion      : 0.00
% 3.29/1.50  Index Deletion       : 0.00
% 3.29/1.50  Index Matching       : 0.00
% 3.29/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
