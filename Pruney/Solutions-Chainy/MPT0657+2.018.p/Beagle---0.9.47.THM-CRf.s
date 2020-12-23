%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  108 (1887 expanded)
%              Number of leaves         :   26 ( 702 expanded)
%              Depth                    :   28
%              Number of atoms          :  235 (6080 expanded)
%              Number of equality atoms :   77 (2478 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_133,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_34,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_527,plain,(
    ! [A_47,B_48,C_49] :
      ( k5_relat_1(k5_relat_1(A_47,B_48),C_49) = k5_relat_1(A_47,k5_relat_1(B_48,C_49))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_225,plain,(
    ! [A_39,B_40] :
      ( k10_relat_1(A_39,k1_relat_1(B_40)) = k1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_111,plain,(
    ! [A_32] :
      ( k10_relat_1(A_32,k2_relat_1(A_32)) = k1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,
    ( k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_111])).

tff(c_132,plain,(
    k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_126])).

tff(c_231,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_132])).

tff(c_249,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_77,c_231])).

tff(c_258,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_36])).

tff(c_14,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_318,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_14])).

tff(c_334,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_318])).

tff(c_544,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_334])).

tff(c_599,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_44,c_544])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k5_relat_1(A_17,B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,
    ( k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_4])).

tff(c_266,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_262])).

tff(c_6,plain,(
    ! [A_4,B_6] :
      ( k10_relat_1(A_4,k1_relat_1(B_6)) = k1_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_341,plain,
    ( k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_6])).

tff(c_348,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_341])).

tff(c_386,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_14])).

tff(c_478,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_481,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_478])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_481])).

tff(c_487,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_780,plain,(
    ! [B_53,A_54] :
      ( k6_relat_1(k1_relat_1(B_53)) = B_53
      | k5_relat_1(A_54,B_53) != A_54
      | k2_relat_1(A_54) != k1_relat_1(B_53)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_788,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k5_relat_1('#skF_1','#skF_2')
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k2_relat_1('#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_780])).

tff(c_813,plain,
    ( k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_487,c_38,c_348,c_348,c_788])).

tff(c_845,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_813])).

tff(c_848,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_845])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_848])).

tff(c_853,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_32,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_relat_1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_18,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,(
    ! [A_36] :
      ( k2_relat_1(k2_funct_1(A_36)) = k1_relat_1(A_36)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1310,plain,(
    ! [A_62] :
      ( k10_relat_1(k2_funct_1(A_62),k1_relat_1(A_62)) = k1_relat_1(k2_funct_1(A_62))
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_4])).

tff(c_942,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_14])).

tff(c_960,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_942])).

tff(c_8,plain,(
    ! [A_7,B_11,C_13] :
      ( k5_relat_1(k5_relat_1(A_7,B_11),C_13) = k5_relat_1(A_7,k5_relat_1(B_11,C_13))
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_974,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_8])).

tff(c_994,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_48,c_974])).

tff(c_12,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_123,plain,(
    ! [A_14] :
      ( k10_relat_1(k6_relat_1(A_14),A_14) = k1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_137,plain,(
    ! [A_33] :
      ( k10_relat_1(k6_relat_1(A_33),A_33) = A_33
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_139,plain,
    ( k10_relat_1(k6_relat_1(k2_relat_1('#skF_1')),k2_relat_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_137])).

tff(c_140,plain,
    ( k10_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_139])).

tff(c_141,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_144,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_144])).

tff(c_150,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_243,plain,(
    ! [A_39] :
      ( k1_relat_1(k5_relat_1(A_39,k5_relat_1('#skF_2','#skF_1'))) = k10_relat_1(A_39,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_225])).

tff(c_254,plain,(
    ! [A_39] :
      ( k1_relat_1(k5_relat_1(A_39,k5_relat_1('#skF_2','#skF_1'))) = k10_relat_1(A_39,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_243])).

tff(c_410,plain,(
    ! [A_43] :
      ( k1_relat_1(k5_relat_1(A_43,k5_relat_1('#skF_2','#skF_1'))) = k10_relat_1(A_43,k1_relat_1('#skF_2'))
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_254])).

tff(c_1098,plain,(
    ! [A_58,A_59] :
      ( k1_relat_1(k5_relat_1(A_58,k5_relat_1(A_59,k5_relat_1('#skF_2','#skF_1')))) = k10_relat_1(A_58,k10_relat_1(A_59,k1_relat_1('#skF_2')))
      | ~ v1_relat_1(k5_relat_1(A_59,k5_relat_1('#skF_2','#skF_1')))
      | ~ v1_relat_1(A_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_6])).

tff(c_1116,plain,(
    ! [A_58] :
      ( k10_relat_1(A_58,k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) = k1_relat_1(k5_relat_1(A_58,'#skF_1'))
      | ~ v1_relat_1(k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')))
      | ~ v1_relat_1(A_58)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_1098])).

tff(c_1163,plain,(
    ! [A_58] :
      ( k10_relat_1(A_58,k1_relat_1('#skF_1')) = k1_relat_1(k5_relat_1(A_58,'#skF_1'))
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_994,c_266,c_1116])).

tff(c_1317,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_1163])).

tff(c_1358,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_1317])).

tff(c_1366,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1358])).

tff(c_1369,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1366])).

tff(c_1373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1369])).

tff(c_1375,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1358])).

tff(c_186,plain,(
    ! [A_35] :
      ( k1_relat_1(k2_funct_1(A_35)) = k2_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1465,plain,(
    ! [A_63] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_63)),k2_funct_1(A_63)) = k2_funct_1(A_63)
      | ~ v1_relat_1(k2_funct_1(A_63))
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_14])).

tff(c_1491,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_1465])).

tff(c_1509,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_1375,c_258,c_1491])).

tff(c_1523,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_8])).

tff(c_1542,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_1375,c_1523])).

tff(c_1571,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1542])).

tff(c_1585,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_599,c_853,c_1571])).

tff(c_1587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.65  
% 3.82/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.66  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.82/1.66  
% 3.82/1.66  %Foreground sorts:
% 3.82/1.66  
% 3.82/1.66  
% 3.82/1.66  %Background operators:
% 3.82/1.66  
% 3.82/1.66  
% 3.82/1.66  %Foreground operators:
% 3.82/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.82/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.82/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.82/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.82/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.66  
% 3.82/1.67  tff(f_133, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 3.82/1.67  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.82/1.67  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.82/1.67  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.82/1.67  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.82/1.67  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.82/1.67  tff(f_80, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 3.82/1.67  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.82/1.67  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 3.82/1.67  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.82/1.67  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.82/1.67  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.82/1.67  tff(c_34, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_40, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_527, plain, (![A_47, B_48, C_49]: (k5_relat_1(k5_relat_1(A_47, B_48), C_49)=k5_relat_1(A_47, k5_relat_1(B_48, C_49)) | ~v1_relat_1(C_49) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.67  tff(c_36, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_10, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.82/1.67  tff(c_77, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_10])).
% 3.82/1.67  tff(c_225, plain, (![A_39, B_40]: (k10_relat_1(A_39, k1_relat_1(B_40))=k1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.67  tff(c_38, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_111, plain, (![A_32]: (k10_relat_1(A_32, k2_relat_1(A_32))=k1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.67  tff(c_126, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_111])).
% 3.82/1.67  tff(c_132, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_126])).
% 3.82/1.67  tff(c_231, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_225, c_132])).
% 3.82/1.67  tff(c_249, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_77, c_231])).
% 3.82/1.67  tff(c_258, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_36])).
% 3.82/1.67  tff(c_14, plain, (![A_15]: (k5_relat_1(k6_relat_1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.67  tff(c_318, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_258, c_14])).
% 3.82/1.67  tff(c_334, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_318])).
% 3.82/1.67  tff(c_544, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_527, c_334])).
% 3.82/1.67  tff(c_599, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_44, c_544])).
% 3.82/1.67  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.82/1.67  tff(c_20, plain, (![A_17, B_18]: (v1_funct_1(k5_relat_1(A_17, B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.82/1.67  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.67  tff(c_4, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.67  tff(c_262, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_249, c_4])).
% 3.82/1.67  tff(c_266, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_262])).
% 3.82/1.67  tff(c_6, plain, (![A_4, B_6]: (k10_relat_1(A_4, k1_relat_1(B_6))=k1_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.82/1.67  tff(c_341, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_6])).
% 3.82/1.67  tff(c_348, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_341])).
% 3.82/1.67  tff(c_386, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_14])).
% 3.82/1.67  tff(c_478, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_386])).
% 3.82/1.67  tff(c_481, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_478])).
% 3.82/1.67  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_481])).
% 3.82/1.67  tff(c_487, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_386])).
% 3.82/1.67  tff(c_780, plain, (![B_53, A_54]: (k6_relat_1(k1_relat_1(B_53))=B_53 | k5_relat_1(A_54, B_53)!=A_54 | k2_relat_1(A_54)!=k1_relat_1(B_53) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.82/1.67  tff(c_788, plain, (k6_relat_1(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k5_relat_1('#skF_1', '#skF_2') | k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_599, c_780])).
% 3.82/1.67  tff(c_813, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_487, c_38, c_348, c_348, c_788])).
% 3.82/1.67  tff(c_845, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_813])).
% 3.82/1.67  tff(c_848, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_845])).
% 3.82/1.67  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_848])).
% 3.82/1.67  tff(c_853, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_813])).
% 3.82/1.67  tff(c_32, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_relat_1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.82/1.67  tff(c_18, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.82/1.67  tff(c_199, plain, (![A_36]: (k2_relat_1(k2_funct_1(A_36))=k1_relat_1(A_36) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.82/1.67  tff(c_1310, plain, (![A_62]: (k10_relat_1(k2_funct_1(A_62), k1_relat_1(A_62))=k1_relat_1(k2_funct_1(A_62)) | ~v1_relat_1(k2_funct_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_199, c_4])).
% 3.82/1.67  tff(c_942, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_853, c_14])).
% 3.82/1.67  tff(c_960, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_942])).
% 3.82/1.67  tff(c_8, plain, (![A_7, B_11, C_13]: (k5_relat_1(k5_relat_1(A_7, B_11), C_13)=k5_relat_1(A_7, k5_relat_1(B_11, C_13)) | ~v1_relat_1(C_13) | ~v1_relat_1(B_11) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.67  tff(c_974, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_960, c_8])).
% 3.82/1.67  tff(c_994, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_48, c_974])).
% 3.82/1.67  tff(c_12, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.82/1.67  tff(c_123, plain, (![A_14]: (k10_relat_1(k6_relat_1(A_14), A_14)=k1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 3.82/1.67  tff(c_137, plain, (![A_33]: (k10_relat_1(k6_relat_1(A_33), A_33)=A_33 | ~v1_relat_1(k6_relat_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 3.82/1.67  tff(c_139, plain, (k10_relat_1(k6_relat_1(k2_relat_1('#skF_1')), k2_relat_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_137])).
% 3.82/1.67  tff(c_140, plain, (k10_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_139])).
% 3.82/1.67  tff(c_141, plain, (~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_140])).
% 3.82/1.67  tff(c_144, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_141])).
% 3.82/1.67  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_144])).
% 3.82/1.67  tff(c_150, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_140])).
% 3.82/1.67  tff(c_243, plain, (![A_39]: (k1_relat_1(k5_relat_1(A_39, k5_relat_1('#skF_2', '#skF_1')))=k10_relat_1(A_39, k2_relat_1('#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_77, c_225])).
% 3.82/1.67  tff(c_254, plain, (![A_39]: (k1_relat_1(k5_relat_1(A_39, k5_relat_1('#skF_2', '#skF_1')))=k10_relat_1(A_39, k2_relat_1('#skF_1')) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_243])).
% 3.82/1.67  tff(c_410, plain, (![A_43]: (k1_relat_1(k5_relat_1(A_43, k5_relat_1('#skF_2', '#skF_1')))=k10_relat_1(A_43, k1_relat_1('#skF_2')) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_254])).
% 3.82/1.67  tff(c_1098, plain, (![A_58, A_59]: (k1_relat_1(k5_relat_1(A_58, k5_relat_1(A_59, k5_relat_1('#skF_2', '#skF_1'))))=k10_relat_1(A_58, k10_relat_1(A_59, k1_relat_1('#skF_2'))) | ~v1_relat_1(k5_relat_1(A_59, k5_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(A_58) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_410, c_6])).
% 3.82/1.67  tff(c_1116, plain, (![A_58]: (k10_relat_1(A_58, k10_relat_1('#skF_1', k1_relat_1('#skF_2')))=k1_relat_1(k5_relat_1(A_58, '#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(A_58) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_994, c_1098])).
% 3.82/1.67  tff(c_1163, plain, (![A_58]: (k10_relat_1(A_58, k1_relat_1('#skF_1'))=k1_relat_1(k5_relat_1(A_58, '#skF_1')) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_994, c_266, c_1116])).
% 3.82/1.67  tff(c_1317, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1310, c_1163])).
% 3.82/1.67  tff(c_1358, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_1317])).
% 3.82/1.67  tff(c_1366, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1358])).
% 3.82/1.67  tff(c_1369, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1366])).
% 3.82/1.67  tff(c_1373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1369])).
% 3.82/1.67  tff(c_1375, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1358])).
% 3.82/1.67  tff(c_186, plain, (![A_35]: (k1_relat_1(k2_funct_1(A_35))=k2_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.82/1.67  tff(c_1465, plain, (![A_63]: (k5_relat_1(k6_relat_1(k2_relat_1(A_63)), k2_funct_1(A_63))=k2_funct_1(A_63) | ~v1_relat_1(k2_funct_1(A_63)) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_186, c_14])).
% 3.82/1.67  tff(c_1491, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_249, c_1465])).
% 3.82/1.67  tff(c_1509, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_1375, c_258, c_1491])).
% 3.82/1.67  tff(c_1523, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_8])).
% 3.82/1.67  tff(c_1542, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_1375, c_1523])).
% 3.82/1.67  tff(c_1571, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1542])).
% 3.82/1.67  tff(c_1585, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_599, c_853, c_1571])).
% 3.82/1.67  tff(c_1587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1585])).
% 3.82/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.67  
% 3.82/1.67  Inference rules
% 3.82/1.67  ----------------------
% 3.82/1.67  #Ref     : 0
% 3.82/1.67  #Sup     : 363
% 3.82/1.67  #Fact    : 0
% 3.82/1.67  #Define  : 0
% 3.82/1.67  #Split   : 6
% 3.82/1.67  #Chain   : 0
% 3.82/1.67  #Close   : 0
% 3.82/1.67  
% 3.82/1.67  Ordering : KBO
% 3.82/1.67  
% 3.82/1.67  Simplification rules
% 3.82/1.67  ----------------------
% 3.82/1.67  #Subsume      : 17
% 3.82/1.67  #Demod        : 546
% 3.82/1.67  #Tautology    : 204
% 3.82/1.67  #SimpNegUnit  : 1
% 3.82/1.68  #BackRed      : 6
% 3.82/1.68  
% 3.82/1.68  #Partial instantiations: 0
% 3.82/1.68  #Strategies tried      : 1
% 3.82/1.68  
% 3.82/1.68  Timing (in seconds)
% 3.82/1.68  ----------------------
% 3.82/1.68  Preprocessing        : 0.34
% 3.82/1.68  Parsing              : 0.19
% 3.82/1.68  CNF conversion       : 0.02
% 3.82/1.68  Main loop            : 0.52
% 3.82/1.68  Inferencing          : 0.18
% 3.82/1.68  Reduction            : 0.19
% 3.82/1.68  Demodulation         : 0.14
% 3.82/1.68  BG Simplification    : 0.03
% 3.82/1.68  Subsumption          : 0.10
% 3.82/1.68  Abstraction          : 0.03
% 3.82/1.68  MUC search           : 0.00
% 3.82/1.68  Cooper               : 0.00
% 3.82/1.68  Total                : 0.91
% 3.82/1.68  Index Insertion      : 0.00
% 3.82/1.68  Index Deletion       : 0.00
% 3.82/1.68  Index Matching       : 0.00
% 3.82/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
