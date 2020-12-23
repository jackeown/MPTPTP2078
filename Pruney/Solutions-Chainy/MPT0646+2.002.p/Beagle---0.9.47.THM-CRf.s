%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.82s
% Verified   : 
% Statistics : Number of formulae       :  127 (2147 expanded)
%              Number of leaves         :   24 ( 812 expanded)
%              Depth                    :   25
%              Number of atoms          :  361 (6092 expanded)
%              Number of equality atoms :   71 (1549 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_420,plain,(
    ! [A_47,B_48,C_49] :
      ( k5_relat_1(k5_relat_1(A_47,B_48),C_49) = k5_relat_1(A_47,k5_relat_1(B_48,C_49))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_125,plain,(
    ! [A_32] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_32)),A_32) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_148,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140])).

tff(c_445,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_148])).

tff(c_489,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_42,c_445])).

tff(c_4,plain,(
    ! [A_4,B_8,C_10] :
      ( k5_relat_1(k5_relat_1(A_4,B_8),C_10) = k5_relat_1(A_4,k5_relat_1(B_8,C_10))
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_512,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_10)) = k5_relat_1('#skF_1',C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_4])).

tff(c_522,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),C_10)) = k5_relat_1('#skF_1',C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_512])).

tff(c_1556,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_522])).

tff(c_1559,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1556])).

tff(c_1563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_1559])).

tff(c_1565,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_522])).

tff(c_22,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_22])).

tff(c_4880,plain,(
    ! [A_118,B_119,C_120,C_121] :
      ( k5_relat_1(k5_relat_1(A_118,k5_relat_1(B_119,C_120)),C_121) = k5_relat_1(k5_relat_1(A_118,B_119),k5_relat_1(C_120,C_121))
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(k5_relat_1(A_118,B_119))
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_420])).

tff(c_20,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_32,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_24,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    v2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_8,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k6_relat_1(k2_relat_1(A_30))) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_108,plain,(
    ! [A_31] : k5_relat_1(k6_relat_1(A_31),k6_relat_1(A_31)) = k6_relat_1(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_120,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k5_relat_1('#skF_1','#skF_2')) = k6_relat_1(k1_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_108])).

tff(c_124,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_120])).

tff(c_442,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_124])).

tff(c_487,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_61,c_442])).

tff(c_798,plain,(
    ! [B_56,A_57] :
      ( v2_funct_1(B_56)
      | k2_relat_1(B_56) != k1_relat_1(A_57)
      | ~ v2_funct_1(k5_relat_1(B_56,A_57))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_813,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_798])).

tff(c_849,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_65,c_813])).

tff(c_850,plain,
    ( k1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_849])).

tff(c_1046,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_1049,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1046])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_61,c_63,c_1049])).

tff(c_1055,plain,(
    v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_59,plain,(
    k2_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_12,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_480,plain,(
    ! [A_47,B_48] :
      ( k5_relat_1(A_47,k5_relat_1(B_48,k6_relat_1(k2_relat_1(k5_relat_1(A_47,B_48))))) = k5_relat_1(A_47,B_48)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_47,B_48))))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47)
      | ~ v1_relat_1(k5_relat_1(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_420])).

tff(c_2209,plain,(
    ! [A_86,B_87] :
      ( k5_relat_1(A_86,k5_relat_1(B_87,k6_relat_1(k2_relat_1(k5_relat_1(A_86,B_87))))) = k5_relat_1(A_86,B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(k5_relat_1(A_86,B_87)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_480])).

tff(c_2428,plain,
    ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k6_relat_1(k2_relat_1(k5_relat_1('#skF_1','#skF_2'))))) = k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_2209])).

tff(c_2561,plain,(
    k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_487,c_42,c_1055,c_34,c_59,c_487,c_2428])).

tff(c_30,plain,(
    ! [B_23,A_21] :
      ( v2_funct_1(B_23)
      | k2_relat_1(B_23) != k1_relat_1(A_21)
      | ~ v2_funct_1(k5_relat_1(B_23,A_21))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2916,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2561,c_30])).

tff(c_2942,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_65,c_2916])).

tff(c_2943,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2942])).

tff(c_4067,plain,(
    ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2943])).

tff(c_4613,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4067])).

tff(c_4624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_61,c_61,c_1055,c_124,c_4613])).

tff(c_4626,plain,(
    v1_relat_1(k5_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2943])).

tff(c_4893,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4880,c_4626])).

tff(c_5162,plain,(
    v1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_38,c_1565,c_38,c_61,c_4893])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v1_funct_1(k5_relat_1(A_14,B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4914,plain,
    ( k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4880,c_2561])).

tff(c_5166,plain,(
    k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_38,c_1565,c_38,c_61,c_4914])).

tff(c_5984,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) != k2_relat_1('#skF_1')
    | ~ v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5166,c_30])).

tff(c_6036,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5162,c_42,c_40,c_65,c_5984])).

tff(c_6037,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) != k2_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6036])).

tff(c_6284,plain,(
    ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_6037])).

tff(c_6290,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1',k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))))
    | ~ v1_relat_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6284])).

tff(c_6298,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_1055,c_487,c_6290])).

tff(c_6307,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_6298])).

tff(c_6314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_61,c_63,c_6307])).

tff(c_6316,plain,(
    v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_6037])).

tff(c_69,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_69])).

tff(c_26,plain,(
    ! [B_20,A_18] :
      ( r1_tarski(k2_relat_1(B_20),k1_relat_1(A_18))
      | k1_relat_1(k5_relat_1(B_20,A_18)) != k1_relat_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_37,B_38] :
      ( k1_relat_1(k5_relat_1(A_37,B_38)) = k1_relat_1(A_37)
      | ~ r1_tarski(k2_relat_1(A_37),k1_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_224,plain,(
    ! [A_11,B_38] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_11),B_38)) = k1_relat_1(k6_relat_1(A_11))
      | ~ r1_tarski(A_11,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_232,plain,(
    ! [A_11,B_38] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_11),B_38)) = A_11
      | ~ r1_tarski(A_11,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_224])).

tff(c_103,plain,(
    ! [A_11] : k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_473,plain,(
    ! [A_11,C_49] :
      ( k5_relat_1(k6_relat_1(A_11),k5_relat_1(k6_relat_1(A_11),C_49)) = k5_relat_1(k6_relat_1(A_11),C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_420])).

tff(c_504,plain,(
    ! [A_11,C_49] :
      ( k5_relat_1(k6_relat_1(A_11),k5_relat_1(k6_relat_1(A_11),C_49)) = k5_relat_1(k6_relat_1(A_11),C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_473])).

tff(c_3172,plain,(
    ! [A_91,B_92,C_93] :
      ( v1_funct_1(k5_relat_1(A_91,k5_relat_1(B_92,C_93)))
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93)
      | ~ v1_funct_1(k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_14])).

tff(c_3275,plain,(
    ! [A_11,C_49] :
      ( v1_funct_1(k5_relat_1(k6_relat_1(A_11),C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_3172])).

tff(c_3395,plain,(
    ! [A_11,C_49] :
      ( v1_funct_1(k5_relat_1(k6_relat_1(A_11),C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_103,c_20,c_103,c_3275])).

tff(c_3722,plain,(
    ! [A_100,B_101,C_102] :
      ( v1_relat_1(k5_relat_1(A_100,k5_relat_1(B_101,C_102)))
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_funct_1(k5_relat_1(A_100,B_101))
      | ~ v1_relat_1(k5_relat_1(A_100,B_101))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_16])).

tff(c_3837,plain,(
    ! [A_11,C_49] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_11),C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_3722])).

tff(c_4627,plain,(
    ! [A_112,C_113] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_112),C_113))
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_103,c_20,c_103,c_3837])).

tff(c_464,plain,(
    ! [C_49] :
      ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',C_49)) = k5_relat_1('#skF_1',C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_420])).

tff(c_591,plain,(
    ! [C_52] :
      ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',C_52)) = k5_relat_1('#skF_1',C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_42,c_464])).

tff(c_628,plain,
    ( k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) = k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_591])).

tff(c_650,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22,c_148,c_628])).

tff(c_657,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10)) = k5_relat_1('#skF_1',C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_1')))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_4])).

tff(c_678,plain,(
    ! [C_10] :
      ( k5_relat_1('#skF_1',k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10)) = k5_relat_1('#skF_1',C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22,c_657])).

tff(c_804,plain,(
    ! [C_10] :
      ( v2_funct_1('#skF_1')
      | k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10)) != k2_relat_1('#skF_1')
      | ~ v2_funct_1(k5_relat_1('#skF_1',C_10))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(C_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_798])).

tff(c_841,plain,(
    ! [C_10] :
      ( v2_funct_1('#skF_1')
      | k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10)) != k2_relat_1('#skF_1')
      | ~ v2_funct_1(k5_relat_1('#skF_1',C_10))
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(C_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_804])).

tff(c_842,plain,(
    ! [C_10] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10)) != k2_relat_1('#skF_1')
      | ~ v2_funct_1(k5_relat_1('#skF_1',C_10))
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_10))
      | ~ v1_relat_1(C_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_841])).

tff(c_15584,plain,(
    ! [C_194] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_194)) != k2_relat_1('#skF_1')
      | ~ v2_funct_1(k5_relat_1('#skF_1',C_194))
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_194))
      | ~ v1_funct_1(C_194)
      | ~ v1_relat_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_4627,c_842])).

tff(c_16590,plain,(
    ! [C_205] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),C_205)) != k2_relat_1('#skF_1')
      | ~ v2_funct_1(k5_relat_1('#skF_1',C_205))
      | ~ v1_funct_1(C_205)
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_3395,c_15584])).

tff(c_16713,plain,(
    ! [B_207] :
      ( ~ v2_funct_1(k5_relat_1('#skF_1',B_207))
      | ~ v1_funct_1(B_207)
      | ~ r1_tarski(k2_relat_1('#skF_1'),k1_relat_1(B_207))
      | ~ v1_relat_1(B_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_16590])).

tff(c_16736,plain,(
    ! [A_18] :
      ( ~ v2_funct_1(k5_relat_1('#skF_1',A_18))
      | k1_relat_1(k5_relat_1('#skF_1',A_18)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_16713])).

tff(c_16932,plain,(
    ! [A_210] :
      ( ~ v2_funct_1(k5_relat_1('#skF_1',A_210))
      | k1_relat_1(k5_relat_1('#skF_1',A_210)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_16736])).

tff(c_16961,plain,
    ( ~ v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_1',k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))))) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5166,c_16932])).

tff(c_17020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5162,c_6316,c_78,c_5166,c_65,c_16961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.83  
% 10.57/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/3.83  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.57/3.83  
% 10.57/3.83  %Foreground sorts:
% 10.57/3.83  
% 10.57/3.83  
% 10.57/3.83  %Background operators:
% 10.57/3.83  
% 10.57/3.83  
% 10.57/3.83  %Foreground operators:
% 10.57/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.57/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.57/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.57/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.57/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.57/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.57/3.83  tff('#skF_2', type, '#skF_2': $i).
% 10.57/3.83  tff('#skF_1', type, '#skF_1': $i).
% 10.57/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.57/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.57/3.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.57/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.57/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.57/3.83  
% 10.82/3.87  tff(f_120, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 10.82/3.87  tff(f_68, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 10.82/3.87  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 10.82/3.87  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 10.82/3.87  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.82/3.87  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.82/3.87  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.82/3.87  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 10.82/3.87  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 10.82/3.87  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 10.82/3.87  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 10.82/3.87  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.82/3.87  tff(c_420, plain, (![A_47, B_48, C_49]: (k5_relat_1(k5_relat_1(A_47, B_48), C_49)=k5_relat_1(A_47, k5_relat_1(B_48, C_49)) | ~v1_relat_1(C_49) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.82/3.87  tff(c_34, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_125, plain, (![A_32]: (k5_relat_1(k6_relat_1(k1_relat_1(A_32)), A_32)=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.82/3.87  tff(c_140, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_125])).
% 10.82/3.87  tff(c_148, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_140])).
% 10.82/3.87  tff(c_445, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_148])).
% 10.82/3.87  tff(c_489, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_42, c_445])).
% 10.82/3.87  tff(c_4, plain, (![A_4, B_8, C_10]: (k5_relat_1(k5_relat_1(A_4, B_8), C_10)=k5_relat_1(A_4, k5_relat_1(B_8, C_10)) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.82/3.87  tff(c_512, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_10))=k5_relat_1('#skF_1', C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_489, c_4])).
% 10.82/3.87  tff(c_522, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), C_10))=k5_relat_1('#skF_1', C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_512])).
% 10.82/3.87  tff(c_1556, plain, (~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_522])).
% 10.82/3.87  tff(c_1559, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1556])).
% 10.82/3.87  tff(c_1563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_40, c_1559])).
% 10.82/3.87  tff(c_1565, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_522])).
% 10.82/3.87  tff(c_22, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.82/3.87  tff(c_61, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_22])).
% 10.82/3.87  tff(c_4880, plain, (![A_118, B_119, C_120, C_121]: (k5_relat_1(k5_relat_1(A_118, k5_relat_1(B_119, C_120)), C_121)=k5_relat_1(k5_relat_1(A_118, B_119), k5_relat_1(C_120, C_121)) | ~v1_relat_1(C_121) | ~v1_relat_1(C_120) | ~v1_relat_1(k5_relat_1(A_118, B_119)) | ~v1_relat_1(C_120) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_4, c_420])).
% 10.82/3.87  tff(c_20, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.82/3.87  tff(c_63, plain, (v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_20])).
% 10.82/3.87  tff(c_32, plain, (~v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.82/3.87  tff(c_24, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.82/3.87  tff(c_65, plain, (v2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_24])).
% 10.82/3.87  tff(c_8, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.82/3.87  tff(c_85, plain, (![A_30]: (k5_relat_1(A_30, k6_relat_1(k2_relat_1(A_30)))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.82/3.87  tff(c_97, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_85])).
% 10.82/3.87  tff(c_108, plain, (![A_31]: (k5_relat_1(k6_relat_1(A_31), k6_relat_1(A_31))=k6_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_97])).
% 10.82/3.87  tff(c_120, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k5_relat_1('#skF_1', '#skF_2'))=k6_relat_1(k1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_108])).
% 10.82/3.87  tff(c_124, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_120])).
% 10.82/3.87  tff(c_442, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_124])).
% 10.82/3.87  tff(c_487, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_61, c_442])).
% 10.82/3.87  tff(c_798, plain, (![B_56, A_57]: (v2_funct_1(B_56) | k2_relat_1(B_56)!=k1_relat_1(A_57) | ~v2_funct_1(k5_relat_1(B_56, A_57)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.82/3.87  tff(c_813, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_487, c_798])).
% 10.82/3.87  tff(c_849, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_65, c_813])).
% 10.82/3.87  tff(c_850, plain, (k1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_849])).
% 10.82/3.87  tff(c_1046, plain, (~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_850])).
% 10.82/3.87  tff(c_1049, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1046])).
% 10.82/3.87  tff(c_1053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_61, c_63, c_1049])).
% 10.82/3.87  tff(c_1055, plain, (v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_850])).
% 10.82/3.87  tff(c_59, plain, (k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_8])).
% 10.82/3.87  tff(c_12, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.82/3.87  tff(c_480, plain, (![A_47, B_48]: (k5_relat_1(A_47, k5_relat_1(B_48, k6_relat_1(k2_relat_1(k5_relat_1(A_47, B_48)))))=k5_relat_1(A_47, B_48) | ~v1_relat_1(k6_relat_1(k2_relat_1(k5_relat_1(A_47, B_48)))) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47) | ~v1_relat_1(k5_relat_1(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_420])).
% 10.82/3.87  tff(c_2209, plain, (![A_86, B_87]: (k5_relat_1(A_86, k5_relat_1(B_87, k6_relat_1(k2_relat_1(k5_relat_1(A_86, B_87)))))=k5_relat_1(A_86, B_87) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86) | ~v1_relat_1(k5_relat_1(A_86, B_87)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_480])).
% 10.82/3.87  tff(c_2428, plain, (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k6_relat_1(k2_relat_1(k5_relat_1('#skF_1', '#skF_2')))))=k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_487, c_2209])).
% 10.82/3.87  tff(c_2561, plain, (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_487, c_42, c_1055, c_34, c_59, c_487, c_2428])).
% 10.82/3.87  tff(c_30, plain, (![B_23, A_21]: (v2_funct_1(B_23) | k2_relat_1(B_23)!=k1_relat_1(A_21) | ~v2_funct_1(k5_relat_1(B_23, A_21)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.82/3.87  tff(c_2916, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2561, c_30])).
% 10.82/3.87  tff(c_2942, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_65, c_2916])).
% 10.82/3.87  tff(c_2943, plain, (k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2942])).
% 10.82/3.87  tff(c_4067, plain, (~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2943])).
% 10.82/3.87  tff(c_4613, plain, (~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2')))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_4067])).
% 10.82/3.87  tff(c_4624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_61, c_61, c_1055, c_124, c_4613])).
% 10.82/3.87  tff(c_4626, plain, (v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_2943])).
% 10.82/3.87  tff(c_4893, plain, (v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4880, c_4626])).
% 10.82/3.87  tff(c_5162, plain, (v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_38, c_1565, c_38, c_61, c_4893])).
% 10.82/3.87  tff(c_14, plain, (![A_14, B_15]: (v1_funct_1(k5_relat_1(A_14, B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.82/3.87  tff(c_4914, plain, (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4880, c_2561])).
% 10.82/3.87  tff(c_5166, plain, (k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_38, c_1565, c_38, c_61, c_4914])).
% 10.82/3.87  tff(c_5984, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))) | ~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_5166, c_30])).
% 10.82/3.87  tff(c_6036, plain, (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5162, c_42, c_40, c_65, c_5984])).
% 10.82/3.87  tff(c_6037, plain, (k1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))!=k2_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_6036])).
% 10.82/3.87  tff(c_6284, plain, (~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_6037])).
% 10.82/3.87  tff(c_6290, plain, (~v1_funct_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))) | ~v1_relat_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_6284])).
% 10.82/3.87  tff(c_6298, plain, (~v1_funct_1(k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_1055, c_487, c_6290])).
% 10.82/3.87  tff(c_6307, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_6298])).
% 10.82/3.87  tff(c_6314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_61, c_63, c_6307])).
% 10.82/3.87  tff(c_6316, plain, (v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_6037])).
% 10.82/3.87  tff(c_69, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.82/3.87  tff(c_78, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_69])).
% 10.82/3.87  tff(c_26, plain, (![B_20, A_18]: (r1_tarski(k2_relat_1(B_20), k1_relat_1(A_18)) | k1_relat_1(k5_relat_1(B_20, A_18))!=k1_relat_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.82/3.87  tff(c_6, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.82/3.87  tff(c_212, plain, (![A_37, B_38]: (k1_relat_1(k5_relat_1(A_37, B_38))=k1_relat_1(A_37) | ~r1_tarski(k2_relat_1(A_37), k1_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.82/3.87  tff(c_224, plain, (![A_11, B_38]: (k1_relat_1(k5_relat_1(k6_relat_1(A_11), B_38))=k1_relat_1(k6_relat_1(A_11)) | ~r1_tarski(A_11, k1_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_212])).
% 10.82/3.87  tff(c_232, plain, (![A_11, B_38]: (k1_relat_1(k5_relat_1(k6_relat_1(A_11), B_38))=A_11 | ~r1_tarski(A_11, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_224])).
% 10.82/3.87  tff(c_103, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_97])).
% 10.82/3.87  tff(c_473, plain, (![A_11, C_49]: (k5_relat_1(k6_relat_1(A_11), k5_relat_1(k6_relat_1(A_11), C_49))=k5_relat_1(k6_relat_1(A_11), C_49) | ~v1_relat_1(C_49) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_420])).
% 10.82/3.87  tff(c_504, plain, (![A_11, C_49]: (k5_relat_1(k6_relat_1(A_11), k5_relat_1(k6_relat_1(A_11), C_49))=k5_relat_1(k6_relat_1(A_11), C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_473])).
% 10.82/3.87  tff(c_3172, plain, (![A_91, B_92, C_93]: (v1_funct_1(k5_relat_1(A_91, k5_relat_1(B_92, C_93))) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93) | ~v1_funct_1(k5_relat_1(A_91, B_92)) | ~v1_relat_1(k5_relat_1(A_91, B_92)) | ~v1_relat_1(C_93) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_420, c_14])).
% 10.82/3.87  tff(c_3275, plain, (![A_11, C_49]: (v1_funct_1(k5_relat_1(k6_relat_1(A_11), C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_funct_1(k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))) | ~v1_relat_1(C_49) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_504, c_3172])).
% 10.82/3.87  tff(c_3395, plain, (![A_11, C_49]: (v1_funct_1(k5_relat_1(k6_relat_1(A_11), C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_103, c_20, c_103, c_3275])).
% 10.82/3.87  tff(c_3722, plain, (![A_100, B_101, C_102]: (v1_relat_1(k5_relat_1(A_100, k5_relat_1(B_101, C_102))) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_funct_1(k5_relat_1(A_100, B_101)) | ~v1_relat_1(k5_relat_1(A_100, B_101)) | ~v1_relat_1(C_102) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_420, c_16])).
% 10.82/3.87  tff(c_3837, plain, (![A_11, C_49]: (v1_relat_1(k5_relat_1(k6_relat_1(A_11), C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_funct_1(k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))) | ~v1_relat_1(C_49) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_504, c_3722])).
% 10.82/3.87  tff(c_4627, plain, (![A_112, C_113]: (v1_relat_1(k5_relat_1(k6_relat_1(A_112), C_113)) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_103, c_20, c_103, c_3837])).
% 10.82/3.87  tff(c_464, plain, (![C_49]: (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', C_49))=k5_relat_1('#skF_1', C_49) | ~v1_relat_1(C_49) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_420])).
% 10.82/3.87  tff(c_591, plain, (![C_52]: (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', C_52))=k5_relat_1('#skF_1', C_52) | ~v1_relat_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_42, c_464])).
% 10.82/3.87  tff(c_628, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))=k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_591])).
% 10.82/3.87  tff(c_650, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22, c_148, c_628])).
% 10.82/3.87  tff(c_657, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10))=k5_relat_1('#skF_1', C_10) | ~v1_relat_1(C_10) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_4])).
% 10.82/3.87  tff(c_678, plain, (![C_10]: (k5_relat_1('#skF_1', k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10))=k5_relat_1('#skF_1', C_10) | ~v1_relat_1(C_10))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22, c_657])).
% 10.82/3.87  tff(c_804, plain, (![C_10]: (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', C_10)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(C_10))), inference(superposition, [status(thm), theory('equality')], [c_678, c_798])).
% 10.82/3.87  tff(c_841, plain, (![C_10]: (v2_funct_1('#skF_1') | k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', C_10)) | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(C_10))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_804])).
% 10.82/3.87  tff(c_842, plain, (![C_10]: (k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', C_10)) | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_10)) | ~v1_relat_1(C_10))), inference(negUnitSimplification, [status(thm)], [c_32, c_841])).
% 10.82/3.87  tff(c_15584, plain, (![C_194]: (k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_194))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', C_194)) | ~v1_funct_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_194)) | ~v1_funct_1(C_194) | ~v1_relat_1(C_194))), inference(resolution, [status(thm)], [c_4627, c_842])).
% 10.82/3.87  tff(c_16590, plain, (![C_205]: (k1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), C_205))!=k2_relat_1('#skF_1') | ~v2_funct_1(k5_relat_1('#skF_1', C_205)) | ~v1_funct_1(C_205) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_3395, c_15584])).
% 10.82/3.87  tff(c_16713, plain, (![B_207]: (~v2_funct_1(k5_relat_1('#skF_1', B_207)) | ~v1_funct_1(B_207) | ~r1_tarski(k2_relat_1('#skF_1'), k1_relat_1(B_207)) | ~v1_relat_1(B_207))), inference(superposition, [status(thm), theory('equality')], [c_232, c_16590])).
% 10.82/3.87  tff(c_16736, plain, (![A_18]: (~v2_funct_1(k5_relat_1('#skF_1', A_18)) | k1_relat_1(k5_relat_1('#skF_1', A_18))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_26, c_16713])).
% 10.82/3.87  tff(c_16932, plain, (![A_210]: (~v2_funct_1(k5_relat_1('#skF_1', A_210)) | k1_relat_1(k5_relat_1('#skF_1', A_210))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_210) | ~v1_relat_1(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_16736])).
% 10.82/3.87  tff(c_16961, plain, (~v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | k1_relat_1(k5_relat_1('#skF_1', k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))))!=k1_relat_1('#skF_1') | ~v1_funct_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2')))) | ~v1_relat_1(k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_5166, c_16932])).
% 10.82/3.87  tff(c_17020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5162, c_6316, c_78, c_5166, c_65, c_16961])).
% 10.82/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.82/3.87  
% 10.82/3.87  Inference rules
% 10.82/3.87  ----------------------
% 10.82/3.87  #Ref     : 0
% 10.82/3.87  #Sup     : 3450
% 10.82/3.87  #Fact    : 0
% 10.82/3.87  #Define  : 0
% 10.82/3.87  #Split   : 21
% 10.82/3.87  #Chain   : 0
% 10.82/3.87  #Close   : 0
% 10.82/3.87  
% 10.82/3.87  Ordering : KBO
% 10.82/3.87  
% 10.82/3.87  Simplification rules
% 10.82/3.87  ----------------------
% 10.82/3.87  #Subsume      : 471
% 10.82/3.87  #Demod        : 10315
% 10.82/3.87  #Tautology    : 1346
% 10.82/3.87  #SimpNegUnit  : 54
% 10.82/3.87  #BackRed      : 20
% 10.82/3.87  
% 10.82/3.87  #Partial instantiations: 0
% 10.82/3.87  #Strategies tried      : 1
% 10.82/3.87  
% 10.82/3.87  Timing (in seconds)
% 10.82/3.87  ----------------------
% 10.82/3.87  Preprocessing        : 0.29
% 10.82/3.87  Parsing              : 0.16
% 10.82/3.87  CNF conversion       : 0.02
% 10.82/3.87  Main loop            : 2.71
% 10.82/3.87  Inferencing          : 0.69
% 10.82/3.87  Reduction            : 1.28
% 10.82/3.87  Demodulation         : 1.07
% 10.82/3.87  BG Simplification    : 0.09
% 10.82/3.87  Subsumption          : 0.53
% 10.82/3.87  Abstraction          : 0.14
% 10.82/3.87  MUC search           : 0.00
% 10.82/3.87  Cooper               : 0.00
% 10.82/3.87  Total                : 3.06
% 10.82/3.87  Index Insertion      : 0.00
% 10.82/3.87  Index Deletion       : 0.00
% 10.82/3.87  Index Matching       : 0.00
% 10.82/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
