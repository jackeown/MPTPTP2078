%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 12.57s
% Output     : CNFRefutation 12.57s
% Verified   : 
% Statistics : Number of formulae       :  148 (36617 expanded)
%              Number of leaves         :   25 (13502 expanded)
%              Depth                    :   35
%              Number of atoms          :  380 (129620 expanded)
%              Number of equality atoms :  128 (46160 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_135,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_117,axiom,(
    ! [A] :
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

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_93,plain,(
    ! [A_32] :
      ( k5_relat_1(A_32,k6_relat_1(k2_relat_1(A_32))) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_93])).

tff(c_117,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_105])).

tff(c_6,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_108,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_119,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108])).

tff(c_26,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_relat_1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_4,B_8,C_10] :
      ( k5_relat_1(k5_relat_1(A_4,B_8),C_10) = k5_relat_1(A_4,k5_relat_1(B_8,C_10))
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_357,plain,(
    ! [A_45,B_46,C_47] :
      ( k5_relat_1(k5_relat_1(A_45,B_46),C_47) = k5_relat_1(A_45,k5_relat_1(B_46,C_47))
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_409,plain,(
    ! [C_47] :
      ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_47)) = k5_relat_1('#skF_1',C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_357])).

tff(c_471,plain,(
    ! [C_49] :
      ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_49)) = k5_relat_1('#skF_1',C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_79,c_409])).

tff(c_484,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1',C_10))) = k5_relat_1('#skF_1',C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_471])).

tff(c_508,plain,(
    ! [C_50] :
      ( k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1',C_50))) = k5_relat_1('#skF_1',C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_484])).

tff(c_530,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1')))) = k5_relat_1('#skF_1',k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_508])).

tff(c_545,plain,
    ( k5_relat_1('#skF_1',k2_funct_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_119,c_530])).

tff(c_550,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_553,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_550])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_553])).

tff(c_558,plain,(
    k5_relat_1('#skF_1',k2_funct_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_569,plain,
    ( k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_26])).

tff(c_580,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_569])).

tff(c_611,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_16])).

tff(c_18,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_609,plain,(
    v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_18])).

tff(c_585,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_119])).

tff(c_604,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_6])).

tff(c_713,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k2_relat_1(B_55),k1_relat_1(A_56))
      | k1_relat_1(k5_relat_1(B_55,A_56)) != k1_relat_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_741,plain,(
    ! [A_56] :
      ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_56))
      | k1_relat_1(k5_relat_1('#skF_2',A_56)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_713])).

tff(c_788,plain,(
    ! [A_57] :
      ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(A_57))
      | k1_relat_1(k5_relat_1('#skF_2',A_57)) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_741])).

tff(c_794,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | k1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) != k1_relat_1('#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_788])).

tff(c_812,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_609,c_585,c_794])).

tff(c_171,plain,(
    ! [A_36,B_37] :
      ( k1_relat_1(k5_relat_1(A_36,B_37)) = k1_relat_1(A_36)
      | ~ r1_tarski(k2_relat_1(A_36),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_37)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_171])).

tff(c_194,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_37)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_183])).

tff(c_820,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_812,c_194])).

tff(c_823,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_72,c_820])).

tff(c_829,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_32])).

tff(c_406,plain,(
    ! [C_47] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_47)) = k5_relat_1('#skF_2',C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_357])).

tff(c_432,plain,(
    ! [C_47] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_47)) = k5_relat_1('#skF_2',C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16,c_406])).

tff(c_1330,plain,(
    ! [C_66] :
      ( k5_relat_1('#skF_2',k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_66)) = k5_relat_1('#skF_2',C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_432])).

tff(c_1350,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_10))) = k5_relat_1('#skF_2',C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1330])).

tff(c_1375,plain,(
    ! [C_67] :
      ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_67))) = k5_relat_1('#skF_2',C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1350])).

tff(c_1410,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2')))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1375])).

tff(c_1433,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_117,c_829,c_1410])).

tff(c_1549,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1433])).

tff(c_22,plain,(
    ! [A_18,B_20] :
      ( v2_funct_1(A_18)
      | k6_relat_1(k1_relat_1(A_18)) != k5_relat_1(A_18,B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1029,plain,(
    ! [B_20] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_20) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_22])).

tff(c_1062,plain,(
    ! [B_20] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_20) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1029])).

tff(c_1551,plain,(
    ! [B_70] :
      ( k5_relat_1('#skF_2',B_70) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1549,c_1062])).

tff(c_1572,plain,(
    ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1551])).

tff(c_1590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1572])).

tff(c_1592,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1433])).

tff(c_24,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_559,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_566,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1(k2_funct_1('#skF_1'),C_10)) = k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_4])).

tff(c_1978,plain,(
    ! [C_80] :
      ( k5_relat_1('#skF_1',k5_relat_1(k2_funct_1('#skF_1'),C_80)) = k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_559,c_566])).

tff(c_2006,plain,
    ( k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1978])).

tff(c_2024,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_44,c_117,c_829,c_823,c_2006])).

tff(c_1591,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_2'))
    | k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1433])).

tff(c_1593,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1591])).

tff(c_1596,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1593])).

tff(c_1600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1596])).

tff(c_1602,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_15247,plain,(
    ! [A_161,C_162] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_161)),C_162) = k5_relat_1(k2_funct_1(A_161),k5_relat_1(A_161,C_162))
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(A_161)
      | ~ v1_relat_1(k2_funct_1(A_161))
      | ~ v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_357])).

tff(c_15452,plain,(
    ! [C_162] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_162) = k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_162))
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_15247])).

tff(c_15547,plain,(
    ! [C_163] :
      ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_163)) = k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1592,c_1602,c_40,c_580,c_15452])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( k2_funct_1(A_22) = B_24
      | k6_relat_1(k1_relat_1(A_22)) != k5_relat_1(A_22,B_24)
      | k2_relat_1(A_22) != k1_relat_1(B_24)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1025,plain,(
    ! [B_24] :
      ( k2_funct_1('#skF_2') = B_24
      | k5_relat_1('#skF_2',B_24) != k5_relat_1('#skF_2','#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_24)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_28])).

tff(c_1059,plain,(
    ! [B_24] :
      ( k2_funct_1('#skF_2') = B_24
      | k5_relat_1('#skF_2',B_24) != k5_relat_1('#skF_2','#skF_1')
      | k1_relat_1(B_24) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_1025])).

tff(c_15054,plain,(
    ! [B_160] :
      ( k2_funct_1('#skF_2') = B_160
      | k5_relat_1('#skF_2',B_160) != k5_relat_1('#skF_2','#skF_1')
      | k1_relat_1(B_160) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1059])).

tff(c_15084,plain,
    ( k2_funct_1('#skF_2') = '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_15054])).

tff(c_15110,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_15084])).

tff(c_77,plain,(
    v1_funct_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_8,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_102,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k6_relat_1(k2_relat_1('#skF_1'))) = k5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_93])).

tff(c_115,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2','#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32,c_102])).

tff(c_617,plain,(
    ! [A_51,B_52] :
      ( v2_funct_1(A_51)
      | k6_relat_1(k1_relat_1(A_51)) != k5_relat_1(A_51,B_52)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_639,plain,
    ( v2_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | k6_relat_1(k1_relat_1(k5_relat_1('#skF_2','#skF_1'))) != k5_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_617])).

tff(c_660,plain,(
    v2_funct_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_77,c_79,c_77,c_32,c_72,c_639])).

tff(c_828,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_75])).

tff(c_827,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_72])).

tff(c_111,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_121,plain,(
    ! [A_11] : k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_641,plain,(
    ! [A_11] :
      ( v2_funct_1(k6_relat_1(A_11))
      | k6_relat_1(k1_relat_1(k6_relat_1(A_11))) != k6_relat_1(A_11)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_617])).

tff(c_662,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_16,c_18,c_6,c_641])).

tff(c_903,plain,(
    ! [A_58,B_59] :
      ( k2_funct_1(A_58) = B_59
      | k6_relat_1(k1_relat_1(A_58)) != k5_relat_1(A_58,B_59)
      | k2_relat_1(A_58) != k1_relat_1(B_59)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_933,plain,(
    ! [A_11] :
      ( k2_funct_1(k6_relat_1(A_11)) = k6_relat_1(A_11)
      | k6_relat_1(k1_relat_1(k6_relat_1(A_11))) != k6_relat_1(A_11)
      | k2_relat_1(k6_relat_1(A_11)) != k1_relat_1(k6_relat_1(A_11))
      | ~ v2_funct_1(k6_relat_1(A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_903])).

tff(c_960,plain,(
    ! [A_11] : k2_funct_1(k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_16,c_18,c_662,c_8,c_6,c_6,c_933])).

tff(c_1023,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k2_funct_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_960])).

tff(c_1057,plain,(
    k2_funct_1(k5_relat_1('#skF_2','#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_1023])).

tff(c_1601,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_10,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1613,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_10)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_4])).

tff(c_3080,plain,(
    ! [C_92] :
      ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),C_92)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1602,c_1613])).

tff(c_3133,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3080])).

tff(c_3161,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_16,c_1601,c_3133])).

tff(c_3204,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))) = k2_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | k6_relat_1(k1_relat_1(k5_relat_1('#skF_2','#skF_1'))) != k5_relat_1('#skF_2','#skF_1')
    | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) != k2_relat_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v2_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))
    | ~ v1_funct_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3161,c_28])).

tff(c_3234,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))) = k5_relat_1('#skF_2','#skF_1')
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_77,c_16,c_18,c_660,c_6,c_828,c_829,c_827,c_1057,c_3204])).

tff(c_3610,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3234])).

tff(c_15137,plain,(
    k2_relat_1('#skF_1') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15110,c_3610])).

tff(c_15166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_15137])).

tff(c_15168,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3234])).

tff(c_15198,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15168,c_10])).

tff(c_15214,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_1')) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_829,c_15198])).

tff(c_15556,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15547,c_15214])).

tff(c_15628,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2024,c_15556])).

tff(c_20838,plain,(
    ! [A_204] :
      ( k2_funct_1(k2_funct_1(A_204)) = A_204
      | k6_relat_1(k1_relat_1(k2_funct_1(A_204))) != k6_relat_1(k2_relat_1(A_204))
      | k2_relat_1(k2_funct_1(A_204)) != k1_relat_1(A_204)
      | ~ v2_funct_1(k2_funct_1(A_204))
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v1_funct_1(k2_funct_1(A_204))
      | ~ v1_relat_1(k2_funct_1(A_204))
      | ~ v2_funct_1(A_204)
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_903])).

tff(c_20841,plain,
    ( k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2'
    | k6_relat_1(k2_relat_1('#skF_2')) != k6_relat_1(k1_relat_1('#skF_1'))
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15628,c_20838])).

tff(c_20852,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1592,c_44,c_15628,c_42,c_15628,c_40,c_38,c_36,c_15628,c_823,c_15628,c_580,c_34,c_580,c_15628,c_20841])).

tff(c_20854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_20852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.57/5.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.57/5.37  
% 12.57/5.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.57/5.37  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 12.57/5.37  
% 12.57/5.37  %Foreground sorts:
% 12.57/5.37  
% 12.57/5.37  
% 12.57/5.37  %Background operators:
% 12.57/5.37  
% 12.57/5.37  
% 12.57/5.37  %Foreground operators:
% 12.57/5.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.57/5.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.57/5.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.57/5.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.57/5.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.57/5.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.57/5.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.57/5.37  tff('#skF_2', type, '#skF_2': $i).
% 12.57/5.37  tff('#skF_1', type, '#skF_1': $i).
% 12.57/5.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.57/5.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.57/5.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.57/5.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.57/5.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.57/5.37  
% 12.57/5.39  tff(f_135, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 12.57/5.39  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 12.57/5.39  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 12.57/5.39  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.57/5.39  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 12.57/5.39  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 12.57/5.39  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.57/5.39  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 12.57/5.39  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 12.57/5.39  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 12.57/5.39  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 12.57/5.39  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_32, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_93, plain, (![A_32]: (k5_relat_1(A_32, k6_relat_1(k2_relat_1(A_32)))=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.57/5.39  tff(c_105, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_93])).
% 12.57/5.39  tff(c_117, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_105])).
% 12.57/5.39  tff(c_6, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.57/5.39  tff(c_72, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 12.57/5.39  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_14, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.57/5.39  tff(c_34, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.57/5.39  tff(c_108, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_93])).
% 12.57/5.39  tff(c_119, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108])).
% 12.57/5.39  tff(c_26, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_relat_1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.57/5.39  tff(c_4, plain, (![A_4, B_8, C_10]: (k5_relat_1(k5_relat_1(A_4, B_8), C_10)=k5_relat_1(A_4, k5_relat_1(B_8, C_10)) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.57/5.39  tff(c_16, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.57/5.39  tff(c_79, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_16])).
% 12.57/5.39  tff(c_357, plain, (![A_45, B_46, C_47]: (k5_relat_1(k5_relat_1(A_45, B_46), C_47)=k5_relat_1(A_45, k5_relat_1(B_46, C_47)) | ~v1_relat_1(C_47) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.57/5.39  tff(c_409, plain, (![C_47]: (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_47))=k5_relat_1('#skF_1', C_47) | ~v1_relat_1(C_47) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_357])).
% 12.57/5.39  tff(c_471, plain, (![C_49]: (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_49))=k5_relat_1('#skF_1', C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_79, c_409])).
% 12.57/5.39  tff(c_484, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', C_10)))=k5_relat_1('#skF_1', C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(C_10) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_471])).
% 12.57/5.39  tff(c_508, plain, (![C_50]: (k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', C_50)))=k5_relat_1('#skF_1', C_50) | ~v1_relat_1(C_50))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_484])).
% 12.57/5.39  tff(c_530, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1'))))=k5_relat_1('#skF_1', k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_508])).
% 12.57/5.39  tff(c_545, plain, (k5_relat_1('#skF_1', k2_funct_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_119, c_530])).
% 12.57/5.39  tff(c_550, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_545])).
% 12.57/5.39  tff(c_553, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_550])).
% 12.57/5.39  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_553])).
% 12.57/5.39  tff(c_558, plain, (k5_relat_1('#skF_1', k2_funct_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_545])).
% 12.57/5.39  tff(c_569, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_558, c_26])).
% 12.57/5.39  tff(c_580, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_569])).
% 12.57/5.39  tff(c_611, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_580, c_16])).
% 12.57/5.39  tff(c_18, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.57/5.39  tff(c_609, plain, (v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_580, c_18])).
% 12.57/5.39  tff(c_585, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_580, c_119])).
% 12.57/5.39  tff(c_604, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_580, c_6])).
% 12.57/5.39  tff(c_713, plain, (![B_55, A_56]: (r1_tarski(k2_relat_1(B_55), k1_relat_1(A_56)) | k1_relat_1(k5_relat_1(B_55, A_56))!=k1_relat_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.57/5.39  tff(c_741, plain, (![A_56]: (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_56)) | k1_relat_1(k5_relat_1('#skF_2', A_56))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_34, c_713])).
% 12.57/5.39  tff(c_788, plain, (![A_57]: (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(A_57)) | k1_relat_1(k5_relat_1('#skF_2', A_57))!=k1_relat_1('#skF_2') | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_741])).
% 12.57/5.39  tff(c_794, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | k1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))!=k1_relat_1('#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_604, c_788])).
% 12.57/5.39  tff(c_812, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_609, c_585, c_794])).
% 12.57/5.39  tff(c_171, plain, (![A_36, B_37]: (k1_relat_1(k5_relat_1(A_36, B_37))=k1_relat_1(A_36) | ~r1_tarski(k2_relat_1(A_36), k1_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.57/5.39  tff(c_183, plain, (![B_37]: (k1_relat_1(k5_relat_1('#skF_2', B_37))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_171])).
% 12.57/5.39  tff(c_194, plain, (![B_37]: (k1_relat_1(k5_relat_1('#skF_2', B_37))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_183])).
% 12.57/5.39  tff(c_820, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_812, c_194])).
% 12.57/5.39  tff(c_823, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_72, c_820])).
% 12.57/5.39  tff(c_829, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_32])).
% 12.57/5.39  tff(c_406, plain, (![C_47]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_47))=k5_relat_1('#skF_2', C_47) | ~v1_relat_1(C_47) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_357])).
% 12.57/5.39  tff(c_432, plain, (![C_47]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_47))=k5_relat_1('#skF_2', C_47) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16, c_406])).
% 12.57/5.39  tff(c_1330, plain, (![C_66]: (k5_relat_1('#skF_2', k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_66))=k5_relat_1('#skF_2', C_66) | ~v1_relat_1(C_66))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_432])).
% 12.57/5.39  tff(c_1350, plain, (![C_10]: (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_10)))=k5_relat_1('#skF_2', C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(C_10) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1330])).
% 12.57/5.39  tff(c_1375, plain, (![C_67]: (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_67)))=k5_relat_1('#skF_2', C_67) | ~v1_relat_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1350])).
% 12.57/5.39  tff(c_1410, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2'))))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1375])).
% 12.57/5.39  tff(c_1433, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_117, c_829, c_1410])).
% 12.57/5.39  tff(c_1549, plain, (~v2_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_1433])).
% 12.57/5.39  tff(c_22, plain, (![A_18, B_20]: (v2_funct_1(A_18) | k6_relat_1(k1_relat_1(A_18))!=k5_relat_1(A_18, B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.57/5.39  tff(c_1029, plain, (![B_20]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_20)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_829, c_22])).
% 12.57/5.39  tff(c_1062, plain, (![B_20]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_20)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1029])).
% 12.57/5.39  tff(c_1551, plain, (![B_70]: (k5_relat_1('#skF_2', B_70)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(negUnitSimplification, [status(thm)], [c_1549, c_1062])).
% 12.57/5.39  tff(c_1572, plain, (~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1551])).
% 12.57/5.39  tff(c_1590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1572])).
% 12.57/5.39  tff(c_1592, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_1433])).
% 12.57/5.39  tff(c_24, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.57/5.39  tff(c_559, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_545])).
% 12.57/5.39  tff(c_566, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1(k2_funct_1('#skF_1'), C_10))=k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_558, c_4])).
% 12.57/5.39  tff(c_1978, plain, (![C_80]: (k5_relat_1('#skF_1', k5_relat_1(k2_funct_1('#skF_1'), C_80))=k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_80) | ~v1_relat_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_559, c_566])).
% 12.57/5.39  tff(c_2006, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1978])).
% 12.57/5.39  tff(c_2024, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_44, c_117, c_829, c_823, c_2006])).
% 12.57/5.39  tff(c_1591, plain, (~v1_relat_1(k2_funct_1('#skF_2')) | k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1433])).
% 12.57/5.39  tff(c_1593, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1591])).
% 12.57/5.39  tff(c_1596, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1593])).
% 12.57/5.39  tff(c_1600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1596])).
% 12.57/5.39  tff(c_1602, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1591])).
% 12.57/5.39  tff(c_15247, plain, (![A_161, C_162]: (k5_relat_1(k6_relat_1(k2_relat_1(A_161)), C_162)=k5_relat_1(k2_funct_1(A_161), k5_relat_1(A_161, C_162)) | ~v1_relat_1(C_162) | ~v1_relat_1(A_161) | ~v1_relat_1(k2_funct_1(A_161)) | ~v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_24, c_357])).
% 12.57/5.39  tff(c_15452, plain, (![C_162]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_162)=k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_162)) | ~v1_relat_1(C_162) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_15247])).
% 12.57/5.39  tff(c_15547, plain, (![C_163]: (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_163))=k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_163) | ~v1_relat_1(C_163))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1592, c_1602, c_40, c_580, c_15452])).
% 12.57/5.39  tff(c_28, plain, (![A_22, B_24]: (k2_funct_1(A_22)=B_24 | k6_relat_1(k1_relat_1(A_22))!=k5_relat_1(A_22, B_24) | k2_relat_1(A_22)!=k1_relat_1(B_24) | ~v2_funct_1(A_22) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.57/5.39  tff(c_1025, plain, (![B_24]: (k2_funct_1('#skF_2')=B_24 | k5_relat_1('#skF_2', B_24)!=k5_relat_1('#skF_2', '#skF_1') | k2_relat_1('#skF_2')!=k1_relat_1(B_24) | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_829, c_28])).
% 12.57/5.39  tff(c_1059, plain, (![B_24]: (k2_funct_1('#skF_2')=B_24 | k5_relat_1('#skF_2', B_24)!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(B_24)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_1025])).
% 12.57/5.39  tff(c_15054, plain, (![B_160]: (k2_funct_1('#skF_2')=B_160 | k5_relat_1('#skF_2', B_160)!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(B_160)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_160) | ~v1_relat_1(B_160))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1059])).
% 12.57/5.39  tff(c_15084, plain, (k2_funct_1('#skF_2')='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_15054])).
% 12.57/5.39  tff(c_15110, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_15084])).
% 12.57/5.39  tff(c_77, plain, (v1_funct_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_18])).
% 12.57/5.39  tff(c_8, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.57/5.39  tff(c_75, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_8])).
% 12.57/5.39  tff(c_102, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k6_relat_1(k2_relat_1('#skF_1')))=k5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_93])).
% 12.57/5.39  tff(c_115, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', '#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32, c_102])).
% 12.57/5.39  tff(c_617, plain, (![A_51, B_52]: (v2_funct_1(A_51) | k6_relat_1(k1_relat_1(A_51))!=k5_relat_1(A_51, B_52) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.57/5.39  tff(c_639, plain, (v2_funct_1(k5_relat_1('#skF_2', '#skF_1')) | k6_relat_1(k1_relat_1(k5_relat_1('#skF_2', '#skF_1')))!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_funct_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_617])).
% 12.57/5.39  tff(c_660, plain, (v2_funct_1(k5_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_77, c_79, c_77, c_32, c_72, c_639])).
% 12.57/5.39  tff(c_828, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_75])).
% 12.57/5.39  tff(c_827, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_823, c_72])).
% 12.57/5.39  tff(c_111, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_93])).
% 12.57/5.39  tff(c_121, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_111])).
% 12.57/5.39  tff(c_641, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)) | k6_relat_1(k1_relat_1(k6_relat_1(A_11)))!=k6_relat_1(A_11) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_617])).
% 12.57/5.39  tff(c_662, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_16, c_18, c_6, c_641])).
% 12.57/5.39  tff(c_903, plain, (![A_58, B_59]: (k2_funct_1(A_58)=B_59 | k6_relat_1(k1_relat_1(A_58))!=k5_relat_1(A_58, B_59) | k2_relat_1(A_58)!=k1_relat_1(B_59) | ~v2_funct_1(A_58) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.57/5.39  tff(c_933, plain, (![A_11]: (k2_funct_1(k6_relat_1(A_11))=k6_relat_1(A_11) | k6_relat_1(k1_relat_1(k6_relat_1(A_11)))!=k6_relat_1(A_11) | k2_relat_1(k6_relat_1(A_11))!=k1_relat_1(k6_relat_1(A_11)) | ~v2_funct_1(k6_relat_1(A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_903])).
% 12.57/5.39  tff(c_960, plain, (![A_11]: (k2_funct_1(k6_relat_1(A_11))=k6_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_16, c_18, c_662, c_8, c_6, c_6, c_933])).
% 12.57/5.39  tff(c_1023, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k2_funct_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_829, c_960])).
% 12.57/5.39  tff(c_1057, plain, (k2_funct_1(k5_relat_1('#skF_2', '#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_829, c_1023])).
% 12.57/5.39  tff(c_1601, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1591])).
% 12.57/5.39  tff(c_10, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.57/5.39  tff(c_1613, plain, (![C_10]: (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_10))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_4])).
% 12.57/5.39  tff(c_3080, plain, (![C_92]: (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), C_92))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_92) | ~v1_relat_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1602, c_1613])).
% 12.57/5.39  tff(c_3133, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3080])).
% 12.57/5.39  tff(c_3161, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1602, c_16, c_1601, c_3133])).
% 12.57/5.39  tff(c_3204, plain, (k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))=k2_funct_1(k5_relat_1('#skF_2', '#skF_1')) | k6_relat_1(k1_relat_1(k5_relat_1('#skF_2', '#skF_1')))!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))))!=k2_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v2_funct_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_funct_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))) | ~v1_funct_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3161, c_28])).
% 12.57/5.39  tff(c_3234, plain, (k6_relat_1(k2_relat_1(k2_funct_1('#skF_2')))=k5_relat_1('#skF_2', '#skF_1') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_77, c_16, c_18, c_660, c_6, c_828, c_829, c_827, c_1057, c_3204])).
% 12.57/5.39  tff(c_3610, plain, (k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_3234])).
% 12.57/5.39  tff(c_15137, plain, (k2_relat_1('#skF_1')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15110, c_3610])).
% 12.57/5.39  tff(c_15166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_823, c_15137])).
% 12.57/5.39  tff(c_15168, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_3234])).
% 12.57/5.39  tff(c_15198, plain, (k5_relat_1(k2_funct_1('#skF_2'), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15168, c_10])).
% 12.57/5.39  tff(c_15214, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_1'))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1602, c_829, c_15198])).
% 12.57/5.39  tff(c_15556, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15547, c_15214])).
% 12.57/5.39  tff(c_15628, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2024, c_15556])).
% 12.57/5.39  tff(c_20838, plain, (![A_204]: (k2_funct_1(k2_funct_1(A_204))=A_204 | k6_relat_1(k1_relat_1(k2_funct_1(A_204)))!=k6_relat_1(k2_relat_1(A_204)) | k2_relat_1(k2_funct_1(A_204))!=k1_relat_1(A_204) | ~v2_funct_1(k2_funct_1(A_204)) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204) | ~v1_funct_1(k2_funct_1(A_204)) | ~v1_relat_1(k2_funct_1(A_204)) | ~v2_funct_1(A_204) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_24, c_903])).
% 12.57/5.39  tff(c_20841, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2' | k6_relat_1(k2_relat_1('#skF_2'))!=k6_relat_1(k1_relat_1('#skF_1')) | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15628, c_20838])).
% 12.57/5.39  tff(c_20852, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1592, c_44, c_15628, c_42, c_15628, c_40, c_38, c_36, c_15628, c_823, c_15628, c_580, c_34, c_580, c_15628, c_20841])).
% 12.57/5.39  tff(c_20854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_20852])).
% 12.57/5.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.57/5.39  
% 12.57/5.39  Inference rules
% 12.57/5.39  ----------------------
% 12.57/5.39  #Ref     : 0
% 12.57/5.39  #Sup     : 4417
% 12.57/5.39  #Fact    : 0
% 12.57/5.39  #Define  : 0
% 12.57/5.39  #Split   : 20
% 12.57/5.39  #Chain   : 0
% 12.57/5.39  #Close   : 0
% 12.57/5.39  
% 12.57/5.39  Ordering : KBO
% 12.57/5.39  
% 12.57/5.39  Simplification rules
% 12.57/5.39  ----------------------
% 12.57/5.39  #Subsume      : 425
% 12.57/5.39  #Demod        : 14142
% 12.57/5.39  #Tautology    : 1487
% 12.57/5.39  #SimpNegUnit  : 52
% 12.57/5.39  #BackRed      : 135
% 12.57/5.39  
% 12.57/5.39  #Partial instantiations: 0
% 12.57/5.39  #Strategies tried      : 1
% 12.57/5.39  
% 12.57/5.39  Timing (in seconds)
% 12.57/5.39  ----------------------
% 12.57/5.40  Preprocessing        : 0.32
% 12.57/5.40  Parsing              : 0.18
% 12.57/5.40  CNF conversion       : 0.02
% 12.57/5.40  Main loop            : 4.28
% 12.57/5.40  Inferencing          : 0.99
% 12.57/5.40  Reduction            : 1.94
% 12.57/5.40  Demodulation         : 1.60
% 12.57/5.40  BG Simplification    : 0.14
% 12.57/5.40  Subsumption          : 1.04
% 12.57/5.40  Abstraction          : 0.23
% 12.57/5.40  MUC search           : 0.00
% 12.57/5.40  Cooper               : 0.00
% 12.57/5.40  Total                : 4.66
% 12.57/5.40  Index Insertion      : 0.00
% 12.57/5.40  Index Deletion       : 0.00
% 12.57/5.40  Index Matching       : 0.00
% 12.57/5.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
