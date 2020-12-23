%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :   89 (1059 expanded)
%              Number of leaves         :   21 ( 398 expanded)
%              Depth                    :   22
%              Number of atoms          :  218 (4007 expanded)
%              Number of equality atoms :   56 (1327 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_106,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    ! [A_32] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_32)),k2_funct_1(A_32)) = k2_funct_1(A_32)
      | ~ v1_relat_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_223,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_202])).

tff(c_233,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_223])).

tff(c_337,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    v2_funct_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_396,plain,(
    ! [B_35,A_36] :
      ( v2_funct_1(B_35)
      | k2_relat_1(B_35) != k1_relat_1(A_36)
      | ~ v2_funct_1(k5_relat_1(B_35,A_36))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_435,plain,
    ( v2_funct_1('#skF_2')
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_396])).

tff(c_462,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_435])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_462])).

tff(c_466,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_8,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_465,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_2'))
    | k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_487,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_490,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_487])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_490])).

tff(c_496,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_220,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_202])).

tff(c_231,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_220])).

tff(c_234,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_237,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_237])).

tff(c_243,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_242,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2])).

tff(c_309,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_243,c_296])).

tff(c_326,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_309])).

tff(c_336,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_326])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_495,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k2_funct_1('#skF_2')) = k2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_506,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k5_relat_1(k2_funct_1('#skF_2'),C_7)) = k5_relat_1(k2_funct_1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_2])).

tff(c_1050,plain,(
    ! [C_43] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k5_relat_1(k2_funct_1('#skF_2'),C_43)) = k5_relat_1(k2_funct_1('#skF_2'),C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_496,c_506])).

tff(c_1075,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k6_relat_1(k2_relat_1('#skF_2'))) = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1050])).

tff(c_1091,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_466,c_36,c_30,c_1075])).

tff(c_476,plain,(
    ! [C_7] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_7)) = k5_relat_1(k2_funct_1('#skF_1'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_2])).

tff(c_484,plain,(
    ! [C_7] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_7)) = k5_relat_1(k2_funct_1('#skF_1'),C_7)
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10,c_476])).

tff(c_1128,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_484])).

tff(c_1144,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1128])).

tff(c_105,plain,(
    ! [A_26,B_27,C_28] :
      ( k5_relat_1(k5_relat_1(A_26,B_27),C_28) = k5_relat_1(A_26,k5_relat_1(B_27,C_28))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1154,plain,(
    ! [A_44,C_45] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_44)),C_45) = k5_relat_1(k2_funct_1(A_44),k5_relat_1(A_44,C_45))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(k2_funct_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_105])).

tff(c_1286,plain,(
    ! [C_45] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_45)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1154])).

tff(c_1461,plain,(
    ! [C_46] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_46)) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_243,c_40,c_1286])).

tff(c_1489,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1461])).

tff(c_1503,plain,(
    k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_243,c_1144,c_242,c_1489])).

tff(c_1504,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1144])).

tff(c_1702,plain,(
    ! [A_47,C_48] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_47)),C_48) = k5_relat_1(A_47,k5_relat_1(k2_funct_1(A_47),C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(k2_funct_1(A_47))
      | ~ v1_relat_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_105])).

tff(c_1733,plain,
    ( k5_relat_1('#skF_1',k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1')))) = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_1091])).

tff(c_1868,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1('#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_40,c_243,c_10,c_1504,c_1733])).

tff(c_1935,plain,
    ( k5_relat_1('#skF_1',k2_funct_1('#skF_1')) = k6_relat_1(k2_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_22])).

tff(c_1954,plain,(
    k5_relat_1('#skF_1',k2_funct_1('#skF_1')) = k6_relat_1(k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_466,c_30,c_1935])).

tff(c_1958,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_relat_1(k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1954,c_1868])).

tff(c_6868,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k5_relat_1(k2_funct_1(A_76),A_76)) = A_76
      | ~ v1_relat_1(A_76)
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v1_relat_1(A_76)
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1702])).

tff(c_7000,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1958,c_6868])).

tff(c_7070,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_34,c_466,c_36,c_496,c_36,c_336,c_7000])).

tff(c_7072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/2.84  
% 8.41/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/2.85  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.41/2.85  
% 8.41/2.85  %Foreground sorts:
% 8.41/2.85  
% 8.41/2.85  
% 8.41/2.85  %Background operators:
% 8.41/2.85  
% 8.41/2.85  
% 8.41/2.85  %Foreground operators:
% 8.41/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.41/2.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.41/2.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.41/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/2.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.41/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.41/2.85  tff('#skF_2', type, '#skF_2': $i).
% 8.41/2.85  tff('#skF_1', type, '#skF_1': $i).
% 8.41/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.41/2.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.41/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.41/2.85  
% 8.41/2.86  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 8.41/2.86  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.41/2.86  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 8.41/2.86  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.41/2.86  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 8.41/2.86  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.41/2.86  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.41/2.86  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 8.41/2.86  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_30, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_66, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.41/2.86  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.41/2.86  tff(c_202, plain, (![A_32]: (k5_relat_1(k6_relat_1(k2_relat_1(A_32)), k2_funct_1(A_32))=k2_funct_1(A_32) | ~v1_relat_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 8.41/2.86  tff(c_223, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_202])).
% 8.41/2.86  tff(c_233, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_223])).
% 8.41/2.86  tff(c_337, plain, (~v2_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_233])).
% 8.41/2.86  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_28, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_12, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.41/2.86  tff(c_51, plain, (v2_funct_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_12])).
% 8.41/2.86  tff(c_396, plain, (![B_35, A_36]: (v2_funct_1(B_35) | k2_relat_1(B_35)!=k1_relat_1(A_36) | ~v2_funct_1(k5_relat_1(B_35, A_36)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.41/2.86  tff(c_435, plain, (v2_funct_1('#skF_2') | k2_relat_1('#skF_2')!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_51, c_396])).
% 8.41/2.86  tff(c_462, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_435])).
% 8.41/2.86  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_462])).
% 8.41/2.86  tff(c_466, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_233])).
% 8.41/2.86  tff(c_8, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.41/2.86  tff(c_465, plain, (~v1_relat_1(k2_funct_1('#skF_2')) | k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_233])).
% 8.41/2.86  tff(c_487, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_465])).
% 8.41/2.86  tff(c_490, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_487])).
% 8.41/2.86  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_490])).
% 8.41/2.86  tff(c_496, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_465])).
% 8.41/2.86  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.41/2.86  tff(c_24, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.41/2.86  tff(c_220, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_202])).
% 8.41/2.86  tff(c_231, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_220])).
% 8.41/2.86  tff(c_234, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_231])).
% 8.41/2.86  tff(c_237, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_234])).
% 8.41/2.86  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_237])).
% 8.41/2.86  tff(c_243, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_231])).
% 8.41/2.86  tff(c_242, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_231])).
% 8.41/2.86  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.41/2.86  tff(c_296, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_2])).
% 8.41/2.86  tff(c_309, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_243, c_296])).
% 8.41/2.86  tff(c_326, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_309])).
% 8.41/2.86  tff(c_336, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_326])).
% 8.41/2.86  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.41/2.86  tff(c_22, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.41/2.86  tff(c_495, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k2_funct_1('#skF_2'))=k2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_465])).
% 8.41/2.86  tff(c_506, plain, (![C_7]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k5_relat_1(k2_funct_1('#skF_2'), C_7))=k5_relat_1(k2_funct_1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_495, c_2])).
% 8.41/2.86  tff(c_1050, plain, (![C_43]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k5_relat_1(k2_funct_1('#skF_2'), C_43))=k5_relat_1(k2_funct_1('#skF_2'), C_43) | ~v1_relat_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_496, c_506])).
% 8.41/2.86  tff(c_1075, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k6_relat_1(k2_relat_1('#skF_2')))=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1050])).
% 8.41/2.86  tff(c_1091, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_466, c_36, c_30, c_1075])).
% 8.41/2.86  tff(c_476, plain, (![C_7]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_7))=k5_relat_1(k2_funct_1('#skF_1'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_2])).
% 8.41/2.86  tff(c_484, plain, (![C_7]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_7))=k5_relat_1(k2_funct_1('#skF_1'), C_7) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10, c_476])).
% 8.41/2.86  tff(c_1128, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_484])).
% 8.41/2.86  tff(c_1144, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1128])).
% 8.41/2.86  tff(c_105, plain, (![A_26, B_27, C_28]: (k5_relat_1(k5_relat_1(A_26, B_27), C_28)=k5_relat_1(A_26, k5_relat_1(B_27, C_28)) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.41/2.86  tff(c_1154, plain, (![A_44, C_45]: (k5_relat_1(k6_relat_1(k2_relat_1(A_44)), C_45)=k5_relat_1(k2_funct_1(A_44), k5_relat_1(A_44, C_45)) | ~v1_relat_1(C_45) | ~v1_relat_1(A_44) | ~v1_relat_1(k2_funct_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_22, c_105])).
% 8.41/2.86  tff(c_1286, plain, (![C_45]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_45))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_45) | ~v1_relat_1(C_45) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1154])).
% 8.41/2.86  tff(c_1461, plain, (![C_46]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_46))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_46) | ~v1_relat_1(C_46))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_243, c_40, c_1286])).
% 8.41/2.86  tff(c_1489, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1461])).
% 8.41/2.86  tff(c_1503, plain, (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_243, c_1144, c_242, c_1489])).
% 8.41/2.86  tff(c_1504, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1144])).
% 8.41/2.86  tff(c_1702, plain, (![A_47, C_48]: (k5_relat_1(k6_relat_1(k1_relat_1(A_47)), C_48)=k5_relat_1(A_47, k5_relat_1(k2_funct_1(A_47), C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(k2_funct_1(A_47)) | ~v1_relat_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_24, c_105])).
% 8.41/2.86  tff(c_1733, plain, (k5_relat_1('#skF_1', k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1'))))=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1702, c_1091])).
% 8.41/2.86  tff(c_1868, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1('#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_40, c_243, c_10, c_1504, c_1733])).
% 8.41/2.86  tff(c_1935, plain, (k5_relat_1('#skF_1', k2_funct_1('#skF_1'))=k6_relat_1(k2_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1868, c_22])).
% 8.41/2.86  tff(c_1954, plain, (k5_relat_1('#skF_1', k2_funct_1('#skF_1'))=k6_relat_1(k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_466, c_30, c_1935])).
% 8.41/2.86  tff(c_1958, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_relat_1(k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1954, c_1868])).
% 8.41/2.86  tff(c_6868, plain, (![A_76]: (k5_relat_1(A_76, k5_relat_1(k2_funct_1(A_76), A_76))=A_76 | ~v1_relat_1(A_76) | ~v1_relat_1(k2_funct_1(A_76)) | ~v1_relat_1(A_76) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1702])).
% 8.41/2.86  tff(c_7000, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1958, c_6868])).
% 8.41/2.86  tff(c_7070, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_34, c_466, c_36, c_496, c_36, c_336, c_7000])).
% 8.41/2.86  tff(c_7072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_7070])).
% 8.41/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/2.86  
% 8.41/2.86  Inference rules
% 8.41/2.86  ----------------------
% 8.41/2.86  #Ref     : 0
% 8.41/2.86  #Sup     : 1509
% 8.41/2.86  #Fact    : 0
% 8.41/2.86  #Define  : 0
% 8.41/2.86  #Split   : 7
% 8.41/2.86  #Chain   : 0
% 8.41/2.86  #Close   : 0
% 8.41/2.86  
% 8.41/2.86  Ordering : KBO
% 8.41/2.86  
% 8.41/2.86  Simplification rules
% 8.41/2.86  ----------------------
% 8.41/2.86  #Subsume      : 16
% 8.41/2.86  #Demod        : 4067
% 8.41/2.86  #Tautology    : 582
% 8.41/2.86  #SimpNegUnit  : 4
% 8.41/2.86  #BackRed      : 7
% 8.41/2.86  
% 8.41/2.86  #Partial instantiations: 0
% 8.41/2.86  #Strategies tried      : 1
% 8.41/2.86  
% 8.41/2.86  Timing (in seconds)
% 8.41/2.86  ----------------------
% 8.41/2.87  Preprocessing        : 0.34
% 8.41/2.87  Parsing              : 0.18
% 8.41/2.87  CNF conversion       : 0.02
% 8.41/2.87  Main loop            : 1.70
% 8.41/2.87  Inferencing          : 0.46
% 8.41/2.87  Reduction            : 0.78
% 8.41/2.87  Demodulation         : 0.63
% 8.41/2.87  BG Simplification    : 0.09
% 8.41/2.87  Subsumption          : 0.30
% 8.41/2.87  Abstraction          : 0.10
% 8.41/2.87  MUC search           : 0.00
% 8.41/2.87  Cooper               : 0.00
% 8.41/2.87  Total                : 2.08
% 8.41/2.87  Index Insertion      : 0.00
% 8.41/2.87  Index Deletion       : 0.00
% 8.41/2.87  Index Matching       : 0.00
% 8.41/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
