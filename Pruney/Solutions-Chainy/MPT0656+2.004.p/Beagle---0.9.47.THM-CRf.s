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
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 236 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  161 ( 719 expanded)
%              Number of equality atoms :   56 ( 243 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_124,negated_conjecture,(
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

tff(f_71,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_106,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_36,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_300,plain,(
    ! [A_43] :
      ( k4_relat_1(A_43) = k2_funct_1(A_43)
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_303,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_300])).

tff(c_306,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_303])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_316,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_2])).

tff(c_324,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_316])).

tff(c_38,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_313,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_4])).

tff(c_322,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_313])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k6_relat_1(k2_relat_1(A_11))) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_338,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_14])).

tff(c_342,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_38,c_338])).

tff(c_40,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_469,plain,(
    ! [A_51,B_52,C_53] :
      ( k5_relat_1(k5_relat_1(A_51,B_52),C_53) = k5_relat_1(A_51,k5_relat_1(B_52,C_53))
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3350,plain,(
    ! [A_111,C_112] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_111)),C_112) = k5_relat_1(k2_funct_1(A_111),k5_relat_1(A_111,C_112))
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(A_111)
      | ~ v1_relat_1(k2_funct_1(A_111))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_469])).

tff(c_3606,plain,(
    ! [C_112] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_112) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_112))
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3350])).

tff(c_3718,plain,(
    ! [C_113] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_113) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_113))
      | ~ v1_relat_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_324,c_50,c_3606])).

tff(c_118,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k6_relat_1(k2_relat_1(A_33))) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,
    ( k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2'))) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_118])).

tff(c_142,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_133])).

tff(c_26,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_18] : v1_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_656,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k2_relat_1(B_56),k1_relat_1(A_57))
      | k1_relat_1(k5_relat_1(B_56,A_57)) != k1_relat_1(B_56)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_683,plain,(
    ! [A_57] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_57))
      | k1_relat_1(k5_relat_1('#skF_1',A_57)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_656])).

tff(c_713,plain,(
    ! [A_58] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_58))
      | k1_relat_1(k5_relat_1('#skF_1',A_58)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_683])).

tff(c_731,plain,(
    ! [A_10] :
      ( r1_tarski(k1_relat_1('#skF_2'),A_10)
      | k1_relat_1(k5_relat_1('#skF_1',k6_relat_1(A_10))) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_713])).

tff(c_742,plain,(
    ! [A_59] :
      ( r1_tarski(k1_relat_1('#skF_2'),A_59)
      | k1_relat_1(k5_relat_1('#skF_1',k6_relat_1(A_59))) != k1_relat_1('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_731])).

tff(c_753,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_742])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_762,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_753,c_18])).

tff(c_766,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_762])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_529,plain,(
    ! [A_12,B_13,C_53] :
      ( k5_relat_1(k6_relat_1(A_12),k5_relat_1(B_13,C_53)) = k5_relat_1(k7_relat_1(B_13,A_12),C_53)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_469])).

tff(c_1245,plain,(
    ! [A_73,B_74,C_75] :
      ( k5_relat_1(k6_relat_1(A_73),k5_relat_1(B_74,C_75)) = k5_relat_1(k7_relat_1(B_74,A_73),C_75)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_529])).

tff(c_1359,plain,(
    ! [A_11,A_73] :
      ( k5_relat_1(k7_relat_1(A_11,A_73),k6_relat_1(k2_relat_1(A_11))) = k5_relat_1(k6_relat_1(A_73),A_11)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1245])).

tff(c_2242,plain,(
    ! [A_99,A_100] :
      ( k5_relat_1(k7_relat_1(A_99,A_100),k6_relat_1(k2_relat_1(A_99))) = k5_relat_1(k6_relat_1(A_100),A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1359])).

tff(c_2286,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_2242])).

tff(c_2329,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2286])).

tff(c_2753,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2329,c_16])).

tff(c_2772,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_766,c_2753])).

tff(c_2776,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2329])).

tff(c_3730,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3718,c_2776])).

tff(c_3859,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_342,c_3730])).

tff(c_3861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.03  
% 5.29/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.03  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.29/2.03  
% 5.29/2.03  %Foreground sorts:
% 5.29/2.03  
% 5.29/2.03  
% 5.29/2.03  %Background operators:
% 5.29/2.03  
% 5.29/2.03  
% 5.29/2.03  %Foreground operators:
% 5.29/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.29/2.03  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.29/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.29/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.03  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.29/2.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.29/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.29/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.29/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.29/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.29/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.29/2.03  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.29/2.03  
% 5.57/2.04  tff(f_124, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.57/2.04  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 5.57/2.04  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.57/2.04  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.57/2.04  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 5.57/2.04  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.57/2.04  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 5.57/2.04  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.57/2.04  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.57/2.04  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 5.57/2.04  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.57/2.04  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.57/2.04  tff(c_36, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_42, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_300, plain, (![A_43]: (k4_relat_1(A_43)=k2_funct_1(A_43) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.57/2.04  tff(c_303, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_300])).
% 5.57/2.04  tff(c_306, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_303])).
% 5.57/2.04  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.57/2.04  tff(c_316, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_306, c_2])).
% 5.57/2.04  tff(c_324, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_316])).
% 5.57/2.04  tff(c_38, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.57/2.04  tff(c_313, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_306, c_4])).
% 5.57/2.04  tff(c_322, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_313])).
% 5.57/2.04  tff(c_14, plain, (![A_11]: (k5_relat_1(A_11, k6_relat_1(k2_relat_1(A_11)))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.57/2.04  tff(c_338, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_14])).
% 5.57/2.04  tff(c_342, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_38, c_338])).
% 5.57/2.04  tff(c_40, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.57/2.04  tff(c_32, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.57/2.04  tff(c_469, plain, (![A_51, B_52, C_53]: (k5_relat_1(k5_relat_1(A_51, B_52), C_53)=k5_relat_1(A_51, k5_relat_1(B_52, C_53)) | ~v1_relat_1(C_53) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.57/2.04  tff(c_3350, plain, (![A_111, C_112]: (k5_relat_1(k6_relat_1(k2_relat_1(A_111)), C_112)=k5_relat_1(k2_funct_1(A_111), k5_relat_1(A_111, C_112)) | ~v1_relat_1(C_112) | ~v1_relat_1(A_111) | ~v1_relat_1(k2_funct_1(A_111)) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_32, c_469])).
% 5.57/2.04  tff(c_3606, plain, (![C_112]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_112)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_112)) | ~v1_relat_1(C_112) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3350])).
% 5.57/2.04  tff(c_3718, plain, (![C_113]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_113)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_113)) | ~v1_relat_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_324, c_50, c_3606])).
% 5.57/2.04  tff(c_118, plain, (![A_33]: (k5_relat_1(A_33, k6_relat_1(k2_relat_1(A_33)))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.57/2.04  tff(c_133, plain, (k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2')))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_118])).
% 5.57/2.04  tff(c_142, plain, (k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_133])).
% 5.57/2.04  tff(c_26, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.57/2.04  tff(c_28, plain, (![A_18]: (v1_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.57/2.04  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.57/2.04  tff(c_656, plain, (![B_56, A_57]: (r1_tarski(k2_relat_1(B_56), k1_relat_1(A_57)) | k1_relat_1(k5_relat_1(B_56, A_57))!=k1_relat_1(B_56) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.57/2.04  tff(c_683, plain, (![A_57]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_57)) | k1_relat_1(k5_relat_1('#skF_1', A_57))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_40, c_656])).
% 5.57/2.04  tff(c_713, plain, (![A_58]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_58)) | k1_relat_1(k5_relat_1('#skF_1', A_58))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_683])).
% 5.57/2.04  tff(c_731, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_2'), A_10) | k1_relat_1(k5_relat_1('#skF_1', k6_relat_1(A_10)))!=k1_relat_1('#skF_1') | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_713])).
% 5.57/2.04  tff(c_742, plain, (![A_59]: (r1_tarski(k1_relat_1('#skF_2'), A_59) | k1_relat_1(k5_relat_1('#skF_1', k6_relat_1(A_59)))!=k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_731])).
% 5.57/2.04  tff(c_753, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_742])).
% 5.57/2.04  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.57/2.04  tff(c_762, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_753, c_18])).
% 5.57/2.04  tff(c_766, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_762])).
% 5.57/2.04  tff(c_16, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.57/2.04  tff(c_529, plain, (![A_12, B_13, C_53]: (k5_relat_1(k6_relat_1(A_12), k5_relat_1(B_13, C_53))=k5_relat_1(k7_relat_1(B_13, A_12), C_53) | ~v1_relat_1(C_53) | ~v1_relat_1(B_13) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(B_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_469])).
% 5.57/2.04  tff(c_1245, plain, (![A_73, B_74, C_75]: (k5_relat_1(k6_relat_1(A_73), k5_relat_1(B_74, C_75))=k5_relat_1(k7_relat_1(B_74, A_73), C_75) | ~v1_relat_1(C_75) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_529])).
% 5.57/2.04  tff(c_1359, plain, (![A_11, A_73]: (k5_relat_1(k7_relat_1(A_11, A_73), k6_relat_1(k2_relat_1(A_11)))=k5_relat_1(k6_relat_1(A_73), A_11) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_11))) | ~v1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1245])).
% 5.57/2.04  tff(c_2242, plain, (![A_99, A_100]: (k5_relat_1(k7_relat_1(A_99, A_100), k6_relat_1(k2_relat_1(A_99)))=k5_relat_1(k6_relat_1(A_100), A_99) | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1359])).
% 5.57/2.04  tff(c_2286, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')=k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_766, c_2242])).
% 5.57/2.04  tff(c_2329, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')=k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2286])).
% 5.57/2.04  tff(c_2753, plain, (k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2')))=k7_relat_1('#skF_2', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2329, c_16])).
% 5.57/2.04  tff(c_2772, plain, (k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_766, c_2753])).
% 5.57/2.04  tff(c_2776, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2329])).
% 5.57/2.04  tff(c_3730, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3718, c_2776])).
% 5.57/2.04  tff(c_3859, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_342, c_3730])).
% 5.57/2.04  tff(c_3861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3859])).
% 5.57/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.04  
% 5.57/2.04  Inference rules
% 5.57/2.04  ----------------------
% 5.57/2.04  #Ref     : 0
% 5.57/2.04  #Sup     : 802
% 5.57/2.04  #Fact    : 0
% 5.57/2.04  #Define  : 0
% 5.57/2.04  #Split   : 6
% 5.57/2.04  #Chain   : 0
% 5.57/2.04  #Close   : 0
% 5.57/2.04  
% 5.57/2.04  Ordering : KBO
% 5.57/2.04  
% 5.57/2.04  Simplification rules
% 5.57/2.04  ----------------------
% 5.57/2.04  #Subsume      : 29
% 5.57/2.04  #Demod        : 1312
% 5.57/2.04  #Tautology    : 337
% 5.57/2.04  #SimpNegUnit  : 1
% 5.57/2.04  #BackRed      : 1
% 5.57/2.04  
% 5.57/2.04  #Partial instantiations: 0
% 5.57/2.04  #Strategies tried      : 1
% 5.57/2.04  
% 5.57/2.04  Timing (in seconds)
% 5.57/2.04  ----------------------
% 5.57/2.05  Preprocessing        : 0.32
% 5.57/2.05  Parsing              : 0.17
% 5.57/2.05  CNF conversion       : 0.02
% 5.57/2.05  Main loop            : 0.93
% 5.57/2.05  Inferencing          : 0.31
% 5.57/2.05  Reduction            : 0.38
% 5.57/2.05  Demodulation         : 0.30
% 5.57/2.05  BG Simplification    : 0.04
% 5.57/2.05  Subsumption          : 0.15
% 5.57/2.05  Abstraction          : 0.05
% 5.57/2.05  MUC search           : 0.00
% 5.57/2.05  Cooper               : 0.00
% 5.57/2.05  Total                : 1.29
% 5.57/2.05  Index Insertion      : 0.00
% 5.57/2.05  Index Deletion       : 0.00
% 5.57/2.05  Index Matching       : 0.00
% 5.57/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
