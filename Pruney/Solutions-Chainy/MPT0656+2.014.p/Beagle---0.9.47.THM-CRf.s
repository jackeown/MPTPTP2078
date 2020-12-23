%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 175 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 637 expanded)
%              Number of equality atoms :   34 ( 199 expanded)
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

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_20,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

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

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k4_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_116,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_103])).

tff(c_24,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_178,plain,(
    ! [A_23,B_24,C_25] :
      ( k5_relat_1(k5_relat_1(A_23,B_24),C_25) = k5_relat_1(A_23,k5_relat_1(B_24,C_25))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_510,plain,(
    ! [A_32,C_33] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_32)),C_33) = k5_relat_1(k2_funct_1(A_32),k5_relat_1(A_32,C_33))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_608,plain,(
    ! [C_33] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_33) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_33))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_510])).

tff(c_619,plain,(
    ! [C_34] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_34) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_34))
      | ~ v1_relat_1(C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_116,c_34,c_608])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_657,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_8])).

tff(c_698,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_657])).

tff(c_22,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4])).

tff(c_120,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24,c_109])).

tff(c_131,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_8])).

tff(c_135,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_131])).

tff(c_649,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_135])).

tff(c_696,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_649])).

tff(c_749,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_696])).

tff(c_759,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_698,c_22,c_749])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:22:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.42  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.98/1.42  
% 2.98/1.42  %Foreground sorts:
% 2.98/1.42  
% 2.98/1.42  
% 2.98/1.42  %Background operators:
% 2.98/1.42  
% 2.98/1.42  
% 2.98/1.42  %Foreground operators:
% 2.98/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.98/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.42  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.98/1.42  
% 2.98/1.44  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 2.98/1.44  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.98/1.44  tff(f_63, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.98/1.44  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.98/1.44  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.98/1.44  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 2.98/1.44  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.98/1.44  tff(c_20, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_84, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.44  tff(c_87, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_84])).
% 2.98/1.44  tff(c_90, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_87])).
% 2.98/1.44  tff(c_14, plain, (![A_11]: (v1_relat_1(k4_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.44  tff(c_103, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_14])).
% 2.98/1.44  tff(c_116, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_103])).
% 2.98/1.44  tff(c_24, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_16, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.44  tff(c_178, plain, (![A_23, B_24, C_25]: (k5_relat_1(k5_relat_1(A_23, B_24), C_25)=k5_relat_1(A_23, k5_relat_1(B_24, C_25)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.44  tff(c_510, plain, (![A_32, C_33]: (k5_relat_1(k6_relat_1(k2_relat_1(A_32)), C_33)=k5_relat_1(k2_funct_1(A_32), k5_relat_1(A_32, C_33)) | ~v1_relat_1(C_33) | ~v1_relat_1(A_32) | ~v1_relat_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_16, c_178])).
% 2.98/1.44  tff(c_608, plain, (![C_33]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_33)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_33)) | ~v1_relat_1(C_33) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_510])).
% 2.98/1.44  tff(c_619, plain, (![C_34]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_34)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_34)) | ~v1_relat_1(C_34))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_116, c_34, c_608])).
% 2.98/1.44  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.44  tff(c_657, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_619, c_8])).
% 2.98/1.44  tff(c_698, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_657])).
% 2.98/1.44  tff(c_22, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.44  tff(c_18, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.44  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.44  tff(c_109, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_4])).
% 2.98/1.44  tff(c_120, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24, c_109])).
% 2.98/1.44  tff(c_131, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_8])).
% 2.98/1.44  tff(c_135, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_131])).
% 2.98/1.44  tff(c_649, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_619, c_135])).
% 2.98/1.44  tff(c_696, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_649])).
% 2.98/1.44  tff(c_749, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_696])).
% 2.98/1.44  tff(c_759, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_698, c_22, c_749])).
% 2.98/1.44  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_759])).
% 2.98/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.44  
% 2.98/1.44  Inference rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Ref     : 0
% 2.98/1.44  #Sup     : 183
% 2.98/1.44  #Fact    : 0
% 2.98/1.44  #Define  : 0
% 2.98/1.44  #Split   : 5
% 2.98/1.44  #Chain   : 0
% 2.98/1.44  #Close   : 0
% 2.98/1.44  
% 2.98/1.44  Ordering : KBO
% 2.98/1.44  
% 2.98/1.44  Simplification rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Subsume      : 32
% 2.98/1.44  #Demod        : 160
% 2.98/1.44  #Tautology    : 56
% 2.98/1.44  #SimpNegUnit  : 1
% 2.98/1.44  #BackRed      : 0
% 2.98/1.44  
% 2.98/1.44  #Partial instantiations: 0
% 2.98/1.44  #Strategies tried      : 1
% 2.98/1.44  
% 2.98/1.44  Timing (in seconds)
% 2.98/1.44  ----------------------
% 2.98/1.44  Preprocessing        : 0.29
% 2.98/1.44  Parsing              : 0.15
% 2.98/1.44  CNF conversion       : 0.02
% 2.98/1.44  Main loop            : 0.38
% 2.98/1.44  Inferencing          : 0.15
% 2.98/1.44  Reduction            : 0.12
% 2.98/1.44  Demodulation         : 0.09
% 2.98/1.44  BG Simplification    : 0.02
% 2.98/1.44  Subsumption          : 0.07
% 2.98/1.44  Abstraction          : 0.02
% 2.98/1.44  MUC search           : 0.00
% 2.98/1.44  Cooper               : 0.00
% 2.98/1.44  Total                : 0.71
% 2.98/1.44  Index Insertion      : 0.00
% 2.98/1.44  Index Deletion       : 0.00
% 2.98/1.44  Index Matching       : 0.00
% 2.98/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
