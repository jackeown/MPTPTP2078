%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:05 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 160 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 492 expanded)
%              Number of equality atoms :   36 ( 180 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_104,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_44,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_28,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_85,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k6_relat_1(k2_relat_1(A_27))) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_103,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_97])).

tff(c_26,plain,(
    ! [A_19] :
      ( k5_relat_1(A_19,k2_funct_1(A_19)) = k6_relat_1(k1_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_856,plain,(
    ! [A_57,B_58,C_59] :
      ( k5_relat_1(k5_relat_1(A_57,B_58),C_59) = k5_relat_1(A_57,k5_relat_1(B_58,C_59))
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_20])).

tff(c_150,plain,(
    ! [A_31] :
      ( k4_relat_1(A_31) = k2_funct_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_156,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_153])).

tff(c_94,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_101,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_94])).

tff(c_57,plain,(
    ! [A_23] : k4_relat_1(k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_69,plain,(
    k4_relat_1(k5_relat_1('#skF_2','#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_161,plain,(
    ! [B_32,A_33] :
      ( k5_relat_1(k4_relat_1(B_32),k4_relat_1(A_33)) = k4_relat_1(k5_relat_1(A_33,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [B_32] :
      ( k5_relat_1(k4_relat_1(B_32),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_161])).

tff(c_300,plain,(
    ! [B_37] :
      ( k5_relat_1(k4_relat_1(B_37),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_173])).

tff(c_312,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_300])).

tff(c_321,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_156,c_101,c_312])).

tff(c_869,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_321])).

tff(c_956,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_869])).

tff(c_994,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_956])).

tff(c_997,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_994])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_997])).

tff(c_1002,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_956])).

tff(c_1052,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1002])).

tff(c_1058,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_103,c_1052])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.23/1.53  
% 3.23/1.53  %Foreground sorts:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Background operators:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Foreground operators:
% 3.23/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.23/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.23/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.23/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.53  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.23/1.53  
% 3.37/1.55  tff(f_104, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 3.37/1.55  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.37/1.55  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.37/1.55  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.37/1.55  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.37/1.55  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.37/1.55  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.37/1.55  tff(f_44, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 3.37/1.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.37/1.55  tff(c_28, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_32, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_85, plain, (![A_27]: (k5_relat_1(A_27, k6_relat_1(k2_relat_1(A_27)))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.37/1.55  tff(c_97, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_85])).
% 3.37/1.55  tff(c_103, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_97])).
% 3.37/1.55  tff(c_26, plain, (![A_19]: (k5_relat_1(A_19, k2_funct_1(A_19))=k6_relat_1(k1_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_18, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.55  tff(c_856, plain, (![A_57, B_58, C_59]: (k5_relat_1(k5_relat_1(A_57, B_58), C_59)=k5_relat_1(A_57, k5_relat_1(B_58, C_59)) | ~v1_relat_1(C_59) | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.37/1.55  tff(c_30, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.55  tff(c_20, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.55  tff(c_53, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_20])).
% 3.37/1.55  tff(c_150, plain, (![A_31]: (k4_relat_1(A_31)=k2_funct_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.55  tff(c_153, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_150])).
% 3.37/1.55  tff(c_156, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_153])).
% 3.37/1.55  tff(c_94, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_85])).
% 3.37/1.55  tff(c_101, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_94])).
% 3.37/1.55  tff(c_57, plain, (![A_23]: (k4_relat_1(k6_relat_1(A_23))=k6_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.37/1.55  tff(c_66, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_57])).
% 3.37/1.55  tff(c_69, plain, (k4_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 3.37/1.55  tff(c_161, plain, (![B_32, A_33]: (k5_relat_1(k4_relat_1(B_32), k4_relat_1(A_33))=k4_relat_1(k5_relat_1(A_33, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.55  tff(c_173, plain, (![B_32]: (k5_relat_1(k4_relat_1(B_32), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_161])).
% 3.37/1.55  tff(c_300, plain, (![B_37]: (k5_relat_1(k4_relat_1(B_37), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_173])).
% 3.37/1.55  tff(c_312, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_300])).
% 3.37/1.55  tff(c_321, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_156, c_101, c_312])).
% 3.37/1.55  tff(c_869, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_856, c_321])).
% 3.37/1.55  tff(c_956, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_869])).
% 3.37/1.55  tff(c_994, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_956])).
% 3.37/1.55  tff(c_997, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_994])).
% 3.37/1.55  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_997])).
% 3.37/1.55  tff(c_1002, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_956])).
% 3.37/1.55  tff(c_1052, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1002])).
% 3.37/1.55  tff(c_1058, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_103, c_1052])).
% 3.37/1.55  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1058])).
% 3.37/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.55  
% 3.37/1.55  Inference rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Ref     : 0
% 3.37/1.55  #Sup     : 235
% 3.37/1.55  #Fact    : 0
% 3.37/1.55  #Define  : 0
% 3.37/1.55  #Split   : 1
% 3.37/1.55  #Chain   : 0
% 3.37/1.55  #Close   : 0
% 3.37/1.55  
% 3.37/1.55  Ordering : KBO
% 3.37/1.55  
% 3.37/1.55  Simplification rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Subsume      : 0
% 3.37/1.55  #Demod        : 204
% 3.37/1.55  #Tautology    : 116
% 3.37/1.55  #SimpNegUnit  : 1
% 3.37/1.55  #BackRed      : 2
% 3.37/1.55  
% 3.37/1.55  #Partial instantiations: 0
% 3.37/1.55  #Strategies tried      : 1
% 3.37/1.55  
% 3.37/1.55  Timing (in seconds)
% 3.37/1.55  ----------------------
% 3.37/1.55  Preprocessing        : 0.34
% 3.37/1.55  Parsing              : 0.18
% 3.37/1.55  CNF conversion       : 0.02
% 3.37/1.55  Main loop            : 0.40
% 3.37/1.55  Inferencing          : 0.15
% 3.37/1.55  Reduction            : 0.15
% 3.37/1.55  Demodulation         : 0.11
% 3.37/1.55  BG Simplification    : 0.02
% 3.37/1.55  Subsumption          : 0.06
% 3.37/1.55  Abstraction          : 0.02
% 3.37/1.55  MUC search           : 0.00
% 3.37/1.55  Cooper               : 0.00
% 3.37/1.55  Total                : 0.77
% 3.37/1.55  Index Insertion      : 0.00
% 3.37/1.55  Index Deletion       : 0.00
% 3.37/1.55  Index Matching       : 0.00
% 3.37/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
