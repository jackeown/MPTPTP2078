%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  97 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 334 expanded)
%              Number of equality atoms :   30 ( 103 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_99,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_81,axiom,(
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

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(c_22,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_83,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_89,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_86])).

tff(c_12,plain,(
    ! [A_11] :
      ( v1_relat_1(k4_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_112,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_105])).

tff(c_24,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_90,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_251,plain,(
    ! [A_28] :
      ( k5_relat_1(k2_funct_1(A_28),k6_relat_1(k1_relat_1(A_28))) = k2_funct_1(A_28)
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_6])).

tff(c_266,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_251])).

tff(c_270,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_112,c_266])).

tff(c_26,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_relat_1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_146,plain,(
    ! [A_24,B_25,C_26] :
      ( k5_relat_1(k5_relat_1(A_24,B_25),C_26) = k5_relat_1(A_24,k5_relat_1(B_25,C_26))
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_403,plain,(
    ! [A_33,C_34] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_33)),C_34) = k5_relat_1(k2_funct_1(A_33),k5_relat_1(A_33,C_34))
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(A_33)
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_146])).

tff(c_512,plain,(
    ! [C_34] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_34) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_34))
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_403])).

tff(c_525,plain,(
    ! [C_35] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_35) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_35))
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_112,c_36,c_512])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_560,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_4])).

tff(c_593,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_270,c_560])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.88/1.40  
% 2.88/1.40  %Foreground sorts:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Background operators:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Foreground operators:
% 2.88/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.88/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.88/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.40  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.88/1.40  
% 2.88/1.41  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.88/1.41  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.88/1.41  tff(f_61, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.88/1.41  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.88/1.41  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.88/1.41  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.88/1.41  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.88/1.41  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.88/1.41  tff(c_22, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_83, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.41  tff(c_86, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_83])).
% 2.88/1.41  tff(c_89, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_86])).
% 2.88/1.41  tff(c_12, plain, (![A_11]: (v1_relat_1(k4_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.41  tff(c_105, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 2.88/1.41  tff(c_112, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_105])).
% 2.88/1.41  tff(c_24, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_90, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.88/1.41  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.41  tff(c_251, plain, (![A_28]: (k5_relat_1(k2_funct_1(A_28), k6_relat_1(k1_relat_1(A_28)))=k2_funct_1(A_28) | ~v1_relat_1(k2_funct_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_90, c_6])).
% 2.88/1.41  tff(c_266, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_251])).
% 2.88/1.41  tff(c_270, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_112, c_266])).
% 2.88/1.41  tff(c_26, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.41  tff(c_18, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.41  tff(c_146, plain, (![A_24, B_25, C_26]: (k5_relat_1(k5_relat_1(A_24, B_25), C_26)=k5_relat_1(A_24, k5_relat_1(B_25, C_26)) | ~v1_relat_1(C_26) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.41  tff(c_403, plain, (![A_33, C_34]: (k5_relat_1(k6_relat_1(k2_relat_1(A_33)), C_34)=k5_relat_1(k2_funct_1(A_33), k5_relat_1(A_33, C_34)) | ~v1_relat_1(C_34) | ~v1_relat_1(A_33) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_18, c_146])).
% 2.88/1.41  tff(c_512, plain, (![C_34]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_34)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_34)) | ~v1_relat_1(C_34) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_403])).
% 2.88/1.41  tff(c_525, plain, (![C_35]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_35)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_35)) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_112, c_36, c_512])).
% 2.88/1.41  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.41  tff(c_560, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_525, c_4])).
% 2.88/1.41  tff(c_593, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_270, c_560])).
% 2.88/1.41  tff(c_595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_593])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 0
% 2.88/1.41  #Sup     : 147
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 3
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 19
% 2.88/1.41  #Demod        : 71
% 2.88/1.41  #Tautology    : 45
% 2.88/1.41  #SimpNegUnit  : 1
% 2.88/1.41  #BackRed      : 0
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.42  Preprocessing        : 0.31
% 2.88/1.42  Parsing              : 0.16
% 2.88/1.42  CNF conversion       : 0.02
% 2.88/1.42  Main loop            : 0.35
% 2.88/1.42  Inferencing          : 0.14
% 2.88/1.42  Reduction            : 0.10
% 2.88/1.42  Demodulation         : 0.07
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.07
% 2.88/1.42  Abstraction          : 0.02
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.69
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
