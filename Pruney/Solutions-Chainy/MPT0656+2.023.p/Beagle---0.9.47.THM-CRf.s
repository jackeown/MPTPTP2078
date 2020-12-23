%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 160 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 583 expanded)
%              Number of equality atoms :   30 ( 194 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

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

tff(c_8,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_61,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_23)),k2_funct_1(A_23)) = k2_funct_1(A_23)
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_174,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_159])).

tff(c_178,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_174])).

tff(c_179,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_233,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_233])).

tff(c_239,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [A_20,B_21,C_22] :
      ( k5_relat_1(k5_relat_1(A_20,B_21),C_22) = k5_relat_1(A_20,k5_relat_1(B_21,C_22))
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_462,plain,(
    ! [A_31,C_32] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_31)),C_32) = k5_relat_1(k2_funct_1(A_31),k5_relat_1(A_31,C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(A_31)
      | ~ v1_relat_1(k2_funct_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_557,plain,(
    ! [C_32] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_32) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_462])).

tff(c_568,plain,(
    ! [C_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_33) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_33))
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_239,c_32,c_557])).

tff(c_602,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_4])).

tff(c_637,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_602])).

tff(c_20,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_238,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_591,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_238])).

tff(c_635,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_591])).

tff(c_686,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_635])).

tff(c_696,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_637,c_20,c_686])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.10/1.48  
% 3.10/1.48  %Foreground sorts:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Background operators:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Foreground operators:
% 3.10/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.10/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.48  
% 3.10/1.49  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.10/1.49  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.10/1.49  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.10/1.49  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.10/1.49  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.10/1.49  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.10/1.49  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_8, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.10/1.49  tff(c_22, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_61, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.49  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.49  tff(c_159, plain, (![A_23]: (k5_relat_1(k6_relat_1(k2_relat_1(A_23)), k2_funct_1(A_23))=k2_funct_1(A_23) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 3.10/1.49  tff(c_174, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_159])).
% 3.10/1.49  tff(c_178, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_174])).
% 3.10/1.49  tff(c_179, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_178])).
% 3.10/1.49  tff(c_233, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_179])).
% 3.10/1.49  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_233])).
% 3.10/1.49  tff(c_239, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_178])).
% 3.10/1.49  tff(c_14, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.49  tff(c_100, plain, (![A_20, B_21, C_22]: (k5_relat_1(k5_relat_1(A_20, B_21), C_22)=k5_relat_1(A_20, k5_relat_1(B_21, C_22)) | ~v1_relat_1(C_22) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.49  tff(c_462, plain, (![A_31, C_32]: (k5_relat_1(k6_relat_1(k2_relat_1(A_31)), C_32)=k5_relat_1(k2_funct_1(A_31), k5_relat_1(A_31, C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(A_31) | ~v1_relat_1(k2_funct_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_100])).
% 3.10/1.49  tff(c_557, plain, (![C_32]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_32)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_462])).
% 3.10/1.49  tff(c_568, plain, (![C_33]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_33)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_33)) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_239, c_32, c_557])).
% 3.10/1.49  tff(c_602, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_568, c_4])).
% 3.10/1.49  tff(c_637, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_602])).
% 3.10/1.49  tff(c_20, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.49  tff(c_16, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.49  tff(c_238, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 3.10/1.49  tff(c_591, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_568, c_238])).
% 3.10/1.49  tff(c_635, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_591])).
% 3.10/1.49  tff(c_686, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_635])).
% 3.10/1.49  tff(c_696, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_637, c_20, c_686])).
% 3.10/1.49  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_696])).
% 3.10/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  
% 3.10/1.49  Inference rules
% 3.10/1.49  ----------------------
% 3.10/1.49  #Ref     : 0
% 3.10/1.49  #Sup     : 169
% 3.10/1.49  #Fact    : 0
% 3.10/1.49  #Define  : 0
% 3.10/1.49  #Split   : 4
% 3.10/1.49  #Chain   : 0
% 3.10/1.49  #Close   : 0
% 3.10/1.49  
% 3.10/1.49  Ordering : KBO
% 3.10/1.49  
% 3.10/1.49  Simplification rules
% 3.10/1.49  ----------------------
% 3.10/1.49  #Subsume      : 25
% 3.10/1.49  #Demod        : 115
% 3.10/1.49  #Tautology    : 48
% 3.10/1.49  #SimpNegUnit  : 1
% 3.10/1.49  #BackRed      : 0
% 3.10/1.49  
% 3.10/1.49  #Partial instantiations: 0
% 3.10/1.49  #Strategies tried      : 1
% 3.10/1.49  
% 3.10/1.49  Timing (in seconds)
% 3.10/1.49  ----------------------
% 3.19/1.50  Preprocessing        : 0.33
% 3.19/1.50  Parsing              : 0.18
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.38
% 3.19/1.50  Inferencing          : 0.15
% 3.19/1.50  Reduction            : 0.11
% 3.19/1.50  Demodulation         : 0.08
% 3.19/1.50  BG Simplification    : 0.03
% 3.19/1.50  Subsumption          : 0.07
% 3.19/1.50  Abstraction          : 0.02
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.74
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
