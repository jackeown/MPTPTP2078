%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:05 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 149 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 470 expanded)
%              Number of equality atoms :   40 ( 156 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_120,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(c_34,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_420,plain,(
    ! [A_46] :
      ( k5_relat_1(A_46,k2_funct_1(A_46)) = k6_relat_1(k1_relat_1(A_46))
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_129,plain,(
    ! [A_30] :
      ( k4_relat_1(A_30) = k2_funct_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_135,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_132])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_2])).

tff(c_153,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_4])).

tff(c_151,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_142])).

tff(c_189,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_32,B_33)),k2_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_198,plain,(
    ! [A_32] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_32,k2_funct_1('#skF_1'))),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_189])).

tff(c_221,plain,(
    ! [A_32] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_32,k2_funct_1('#skF_1'))),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_198])).

tff(c_427,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1('#skF_1'))),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_221])).

tff(c_436,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_48,c_14,c_427])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_246,plain,(
    ! [B_36,A_37] :
      ( k5_relat_1(B_36,k6_relat_1(A_37)) = B_36
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_273,plain,(
    ! [A_37] :
      ( k5_relat_1('#skF_2',k6_relat_1(A_37)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_37)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_246])).

tff(c_283,plain,(
    ! [A_37] :
      ( k5_relat_1('#skF_2',k6_relat_1(A_37)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_273])).

tff(c_443,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_436,c_283])).

tff(c_32,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k2_funct_1(A_20)) = k6_relat_1(k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_721,plain,(
    ! [A_55,B_56,C_57] :
      ( k5_relat_1(k5_relat_1(A_55,B_56),C_57) = k5_relat_1(A_55,k5_relat_1(B_56,C_57))
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6])).

tff(c_149,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_139])).

tff(c_16,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_14)),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_16])).

tff(c_162,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_36,c_158])).

tff(c_749,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_162])).

tff(c_802,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_153,c_749])).

tff(c_826,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_802])).

tff(c_834,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_443,c_826])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  
% 3.16/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.16/1.56  
% 3.16/1.56  %Foreground sorts:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Background operators:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Foreground operators:
% 3.16/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.16/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.56  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.16/1.56  
% 3.16/1.58  tff(f_120, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 3.16/1.58  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.16/1.58  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 3.16/1.58  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.16/1.58  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.16/1.58  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.16/1.58  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.16/1.58  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.16/1.58  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.16/1.58  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 3.16/1.58  tff(c_34, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_40, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.58  tff(c_420, plain, (![A_46]: (k5_relat_1(A_46, k2_funct_1(A_46))=k6_relat_1(k1_relat_1(A_46)) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.58  tff(c_129, plain, (![A_30]: (k4_relat_1(A_30)=k2_funct_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.58  tff(c_132, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_40, c_129])).
% 3.16/1.58  tff(c_135, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_132])).
% 3.16/1.58  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.58  tff(c_145, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_2])).
% 3.16/1.58  tff(c_153, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145])).
% 3.16/1.58  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.58  tff(c_142, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_4])).
% 3.16/1.58  tff(c_151, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_142])).
% 3.16/1.58  tff(c_189, plain, (![A_32, B_33]: (r1_tarski(k2_relat_1(k5_relat_1(A_32, B_33)), k2_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.58  tff(c_198, plain, (![A_32]: (r1_tarski(k2_relat_1(k5_relat_1(A_32, k2_funct_1('#skF_1'))), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_151, c_189])).
% 3.16/1.58  tff(c_221, plain, (![A_32]: (r1_tarski(k2_relat_1(k5_relat_1(A_32, k2_funct_1('#skF_1'))), k1_relat_1('#skF_1')) | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_198])).
% 3.16/1.58  tff(c_427, plain, (r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1('#skF_1'))), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_221])).
% 3.16/1.58  tff(c_436, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_48, c_14, c_427])).
% 3.16/1.58  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_38, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_246, plain, (![B_36, A_37]: (k5_relat_1(B_36, k6_relat_1(A_37))=B_36 | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.58  tff(c_273, plain, (![A_37]: (k5_relat_1('#skF_2', k6_relat_1(A_37))='#skF_2' | ~r1_tarski(k1_relat_1('#skF_1'), A_37) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_246])).
% 3.16/1.58  tff(c_283, plain, (![A_37]: (k5_relat_1('#skF_2', k6_relat_1(A_37))='#skF_2' | ~r1_tarski(k1_relat_1('#skF_1'), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_273])).
% 3.16/1.58  tff(c_443, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(resolution, [status(thm)], [c_436, c_283])).
% 3.16/1.58  tff(c_32, plain, (![A_20]: (k5_relat_1(A_20, k2_funct_1(A_20))=k6_relat_1(k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.58  tff(c_721, plain, (![A_55, B_56, C_57]: (k5_relat_1(k5_relat_1(A_55, B_56), C_57)=k5_relat_1(A_55, k5_relat_1(B_56, C_57)) | ~v1_relat_1(C_57) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.58  tff(c_36, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.58  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.58  tff(c_139, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_6])).
% 3.16/1.58  tff(c_149, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_139])).
% 3.16/1.58  tff(c_16, plain, (![A_14]: (k5_relat_1(k6_relat_1(k1_relat_1(A_14)), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.58  tff(c_158, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_16])).
% 3.16/1.58  tff(c_162, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_36, c_158])).
% 3.16/1.58  tff(c_749, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_721, c_162])).
% 3.16/1.58  tff(c_802, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_153, c_749])).
% 3.16/1.58  tff(c_826, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_802])).
% 3.16/1.58  tff(c_834, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_443, c_826])).
% 3.16/1.58  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_834])).
% 3.16/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.58  
% 3.16/1.58  Inference rules
% 3.16/1.58  ----------------------
% 3.16/1.58  #Ref     : 0
% 3.16/1.58  #Sup     : 192
% 3.16/1.58  #Fact    : 0
% 3.16/1.58  #Define  : 0
% 3.16/1.58  #Split   : 6
% 3.16/1.58  #Chain   : 0
% 3.16/1.58  #Close   : 0
% 3.16/1.58  
% 3.16/1.58  Ordering : KBO
% 3.16/1.58  
% 3.16/1.58  Simplification rules
% 3.16/1.58  ----------------------
% 3.16/1.58  #Subsume      : 30
% 3.16/1.58  #Demod        : 183
% 3.16/1.58  #Tautology    : 70
% 3.16/1.58  #SimpNegUnit  : 1
% 3.16/1.58  #BackRed      : 0
% 3.16/1.58  
% 3.16/1.58  #Partial instantiations: 0
% 3.16/1.58  #Strategies tried      : 1
% 3.16/1.58  
% 3.16/1.58  Timing (in seconds)
% 3.16/1.58  ----------------------
% 3.16/1.58  Preprocessing        : 0.37
% 3.16/1.58  Parsing              : 0.21
% 3.16/1.58  CNF conversion       : 0.02
% 3.16/1.58  Main loop            : 0.43
% 3.16/1.58  Inferencing          : 0.16
% 3.16/1.58  Reduction            : 0.14
% 3.16/1.58  Demodulation         : 0.10
% 3.16/1.58  BG Simplification    : 0.02
% 3.16/1.58  Subsumption          : 0.07
% 3.16/1.58  Abstraction          : 0.02
% 3.16/1.58  MUC search           : 0.00
% 3.16/1.58  Cooper               : 0.00
% 3.16/1.58  Total                : 0.83
% 3.16/1.58  Index Insertion      : 0.00
% 3.16/1.58  Index Deletion       : 0.00
% 3.16/1.58  Index Matching       : 0.00
% 3.16/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
