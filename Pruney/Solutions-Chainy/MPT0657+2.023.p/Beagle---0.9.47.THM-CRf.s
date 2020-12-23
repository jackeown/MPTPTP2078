%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 163 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 629 expanded)
%              Number of equality atoms :   34 ( 197 expanded)
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
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

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

tff(c_22,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_43,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_relat_1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_61,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_55])).

tff(c_16,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    ! [A_20,B_21,C_22] :
      ( k5_relat_1(k5_relat_1(A_20,B_21),C_22) = k5_relat_1(A_20,k5_relat_1(B_21,C_22))
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    ! [A_26,C_27] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_26)),C_27) = k5_relat_1(k2_funct_1(A_26),k5_relat_1(A_26,C_27))
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(A_26)
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_303,plain,(
    ! [C_27] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_27)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_312,plain,(
    ! [C_27] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_27)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_32,c_303])).

tff(c_433,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_436,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_433])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_436])).

tff(c_442,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_444,plain,(
    ! [C_30] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_30)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_464,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_444])).

tff(c_481,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_442,c_464])).

tff(c_79,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k6_relat_1(k2_relat_1(A_8))) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_17] :
      ( k5_relat_1(k2_funct_1(A_17),k6_relat_1(k1_relat_1(A_17))) = k2_funct_1(A_17)
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_490,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_85])).

tff(c_502,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_442,c_490])).

tff(c_522,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_502])).

tff(c_532,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_442,c_522])).

tff(c_732,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_532])).

tff(c_740,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_61,c_732])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.44  
% 2.72/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.44  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.72/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.72/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.44  
% 2.72/1.46  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 2.72/1.46  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.72/1.46  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.72/1.46  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.72/1.46  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.72/1.46  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.72/1.46  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_22, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_43, plain, (![A_15]: (k5_relat_1(A_15, k6_relat_1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.46  tff(c_55, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_43])).
% 2.72/1.46  tff(c_61, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_55])).
% 2.72/1.46  tff(c_16, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.46  tff(c_8, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.46  tff(c_20, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.46  tff(c_14, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.46  tff(c_109, plain, (![A_20, B_21, C_22]: (k5_relat_1(k5_relat_1(A_20, B_21), C_22)=k5_relat_1(A_20, k5_relat_1(B_21, C_22)) | ~v1_relat_1(C_22) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.46  tff(c_225, plain, (![A_26, C_27]: (k5_relat_1(k6_relat_1(k2_relat_1(A_26)), C_27)=k5_relat_1(k2_funct_1(A_26), k5_relat_1(A_26, C_27)) | ~v1_relat_1(C_27) | ~v1_relat_1(A_26) | ~v1_relat_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_14, c_109])).
% 2.72/1.46  tff(c_303, plain, (![C_27]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_27))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_27) | ~v1_relat_1(C_27) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_225])).
% 2.72/1.46  tff(c_312, plain, (![C_27]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_27))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_27) | ~v1_relat_1(C_27) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_32, c_303])).
% 2.72/1.46  tff(c_433, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_312])).
% 2.72/1.46  tff(c_436, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_433])).
% 2.72/1.46  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_436])).
% 2.72/1.46  tff(c_442, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_312])).
% 2.72/1.46  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.46  tff(c_444, plain, (![C_30]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_30))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_30) | ~v1_relat_1(C_30))), inference(splitRight, [status(thm)], [c_312])).
% 2.72/1.46  tff(c_464, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_444])).
% 2.72/1.46  tff(c_481, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_442, c_464])).
% 2.72/1.46  tff(c_79, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.46  tff(c_4, plain, (![A_8]: (k5_relat_1(A_8, k6_relat_1(k2_relat_1(A_8)))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.46  tff(c_85, plain, (![A_17]: (k5_relat_1(k2_funct_1(A_17), k6_relat_1(k1_relat_1(A_17)))=k2_funct_1(A_17) | ~v1_relat_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 2.72/1.46  tff(c_490, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_481, c_85])).
% 2.72/1.46  tff(c_502, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_442, c_490])).
% 2.72/1.46  tff(c_522, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_502])).
% 2.72/1.46  tff(c_532, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_442, c_522])).
% 2.72/1.46  tff(c_732, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_532])).
% 2.72/1.46  tff(c_740, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_61, c_732])).
% 2.72/1.46  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_740])).
% 2.72/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.46  
% 2.72/1.46  Inference rules
% 2.72/1.46  ----------------------
% 2.72/1.46  #Ref     : 0
% 2.72/1.46  #Sup     : 179
% 2.72/1.46  #Fact    : 0
% 2.72/1.46  #Define  : 0
% 2.72/1.46  #Split   : 4
% 2.72/1.46  #Chain   : 0
% 2.72/1.46  #Close   : 0
% 2.72/1.46  
% 2.72/1.46  Ordering : KBO
% 2.72/1.46  
% 2.72/1.46  Simplification rules
% 2.72/1.46  ----------------------
% 2.72/1.46  #Subsume      : 15
% 2.72/1.46  #Demod        : 106
% 2.72/1.46  #Tautology    : 47
% 2.72/1.46  #SimpNegUnit  : 1
% 2.72/1.46  #BackRed      : 1
% 2.72/1.46  
% 2.72/1.46  #Partial instantiations: 0
% 2.72/1.46  #Strategies tried      : 1
% 2.72/1.46  
% 2.72/1.46  Timing (in seconds)
% 2.72/1.46  ----------------------
% 2.72/1.46  Preprocessing        : 0.30
% 2.72/1.46  Parsing              : 0.16
% 2.72/1.46  CNF conversion       : 0.02
% 2.72/1.46  Main loop            : 0.41
% 2.72/1.46  Inferencing          : 0.16
% 2.72/1.46  Reduction            : 0.12
% 2.72/1.46  Demodulation         : 0.09
% 2.72/1.46  BG Simplification    : 0.03
% 2.72/1.46  Subsumption          : 0.08
% 2.72/1.46  Abstraction          : 0.02
% 2.72/1.46  MUC search           : 0.00
% 2.72/1.46  Cooper               : 0.00
% 2.72/1.46  Total                : 0.74
% 2.72/1.46  Index Insertion      : 0.00
% 2.72/1.46  Index Deletion       : 0.00
% 2.72/1.46  Index Matching       : 0.00
% 2.72/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
