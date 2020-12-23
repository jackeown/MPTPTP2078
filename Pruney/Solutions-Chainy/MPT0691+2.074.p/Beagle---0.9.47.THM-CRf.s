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
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 689 expanded)
%              Number of leaves         :   25 ( 260 expanded)
%              Depth                    :   20
%              Number of atoms          :  189 (1335 expanded)
%              Number of equality atoms :   56 ( 486 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_26] :
      ( k9_relat_1(A_26,k1_relat_1(A_26)) = k2_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_16] :
      ( k9_relat_1(k6_relat_1(A_16),A_16) = k2_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_51])).

tff(c_64,plain,(
    ! [A_16] : k9_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_60])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75,plain,(
    ! [A_30] :
      ( k10_relat_1(A_30,k2_relat_1(A_30)) = k1_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_84,plain,(
    ! [A_16] :
      ( k10_relat_1(k6_relat_1(A_16),A_16) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_75])).

tff(c_88,plain,(
    ! [A_16] : k10_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_84])).

tff(c_118,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k9_relat_1(B_36,k10_relat_1(B_36,A_37)),A_37)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_16),A_16),A_16)
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_118])).

tff(c_126,plain,(
    ! [A_16] : r1_tarski(A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_64,c_121])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_98,plain,(
    ! [B_32,A_33] :
      ( k5_relat_1(B_32,k6_relat_1(A_33)) = B_32
      | ~ r1_tarski(k2_relat_1(B_32),A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ! [A_16,A_33] :
      ( k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_33)) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_33)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_103,plain,(
    ! [A_16,A_33] :
      ( k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_33)) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_101])).

tff(c_127,plain,(
    ! [A_38,B_39] :
      ( k10_relat_1(A_38,k1_relat_1(B_39)) = k1_relat_1(k5_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    ! [A_38,A_16] :
      ( k1_relat_1(k5_relat_1(A_38,k6_relat_1(A_16))) = k10_relat_1(A_38,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_258,plain,(
    ! [A_46,A_47] :
      ( k1_relat_1(k5_relat_1(A_46,k6_relat_1(A_47))) = k10_relat_1(A_46,A_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_279,plain,(
    ! [A_16,A_33] :
      ( k10_relat_1(k6_relat_1(A_16),A_33) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ r1_tarski(A_16,A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_258])).

tff(c_285,plain,(
    ! [A_16,A_33] :
      ( k10_relat_1(k6_relat_1(A_16),A_33) = A_16
      | ~ r1_tarski(A_16,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_279])).

tff(c_411,plain,(
    ! [B_53,C_54,A_55] :
      ( k10_relat_1(k5_relat_1(B_53,C_54),A_55) = k10_relat_1(B_53,k10_relat_1(C_54,A_55))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_441,plain,(
    ! [A_16,A_33,A_55] :
      ( k10_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_33),A_55)) = k10_relat_1(k6_relat_1(A_16),A_55)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ r1_tarski(A_16,A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_411])).

tff(c_1718,plain,(
    ! [A_99,A_100,A_101] :
      ( k10_relat_1(k6_relat_1(A_99),k10_relat_1(k6_relat_1(A_100),A_101)) = k10_relat_1(k6_relat_1(A_99),A_101)
      | ~ r1_tarski(A_99,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_441])).

tff(c_1871,plain,(
    ! [A_102,A_103,A_104] :
      ( k10_relat_1(k6_relat_1(A_102),A_103) = A_102
      | ~ r1_tarski(A_102,k10_relat_1(k6_relat_1(A_104),A_103))
      | ~ r1_tarski(A_102,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_285])).

tff(c_2413,plain,(
    ! [A_116,A_117,A_118] :
      ( k10_relat_1(k6_relat_1(A_116),A_117) = A_116
      | ~ r1_tarski(A_116,A_118)
      | ~ r1_tarski(A_116,A_118)
      | ~ r1_tarski(A_118,A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_1871])).

tff(c_2443,plain,(
    ! [A_117] :
      ( k10_relat_1(k6_relat_1('#skF_1'),A_117) = '#skF_1'
      | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_117) ) ),
    inference(resolution,[status(thm)],[c_28,c_2413])).

tff(c_2465,plain,(
    ! [A_119] :
      ( k10_relat_1(k6_relat_1('#skF_1'),A_119) = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2443])).

tff(c_2485,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_126,c_2465])).

tff(c_12,plain,(
    ! [A_13,B_15] :
      ( k10_relat_1(A_13,k1_relat_1(B_15)) = k1_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2530,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2485,c_12])).

tff(c_2568,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_2530])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [B_43,C_44,A_45] :
      ( k9_relat_1(k5_relat_1(B_43,C_44),A_45) = k9_relat_1(C_44,k9_relat_1(B_43,A_45))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    ! [C_44,B_43] :
      ( k9_relat_1(C_44,k9_relat_1(B_43,k1_relat_1(k5_relat_1(B_43,C_44)))) = k2_relat_1(k5_relat_1(B_43,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(k5_relat_1(B_43,C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_222])).

tff(c_2585,plain,
    ( k9_relat_1('#skF_2',k9_relat_1(k6_relat_1('#skF_1'),'#skF_1')) = k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2568,c_249])).

tff(c_2621,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_64,c_2585])).

tff(c_4069,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2621])).

tff(c_4072,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_4069])).

tff(c_4076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_4072])).

tff(c_4078,plain,(
    v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2621])).

tff(c_4077,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2621])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_445,plain,(
    ! [B_53,C_54] :
      ( k10_relat_1(B_53,k10_relat_1(C_54,k2_relat_1(k5_relat_1(B_53,C_54)))) = k1_relat_1(k5_relat_1(B_53,C_54))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k5_relat_1(B_53,C_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_411])).

tff(c_4144,plain,
    ( k10_relat_1(k6_relat_1('#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4077,c_445])).

tff(c_4173,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4078,c_20,c_30,c_2568,c_4144])).

tff(c_156,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_64,c_121])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_162,plain,(
    ! [B_41] :
      ( k5_relat_1(B_41,k6_relat_1(k2_relat_1(B_41))) = B_41
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_156,c_18])).

tff(c_182,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_16)) = k6_relat_1(A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_162])).

tff(c_194,plain,(
    ! [A_16] : k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_16)) = k6_relat_1(A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_182])).

tff(c_3107,plain,(
    ! [B_129,C_130,B_131] :
      ( k10_relat_1(B_129,k10_relat_1(C_130,k1_relat_1(B_131))) = k1_relat_1(k5_relat_1(k5_relat_1(B_129,C_130),B_131))
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(k5_relat_1(B_129,C_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_411])).

tff(c_431,plain,(
    ! [A_16,A_55] :
      ( k10_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_16),A_55)) = k10_relat_1(k6_relat_1(A_16),A_55)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_411])).

tff(c_449,plain,(
    ! [A_16,A_55] : k10_relat_1(k6_relat_1(A_16),k10_relat_1(k6_relat_1(A_16),A_55)) = k10_relat_1(k6_relat_1(A_16),A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_431])).

tff(c_3180,plain,(
    ! [A_16,B_131] :
      ( k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_16)),B_131)) = k10_relat_1(k6_relat_1(A_16),k1_relat_1(B_131))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_16),k6_relat_1(A_16))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3107,c_449])).

tff(c_3330,plain,(
    ! [A_132,B_133] :
      ( k10_relat_1(k6_relat_1(A_132),k1_relat_1(B_133)) = k1_relat_1(k5_relat_1(k6_relat_1(A_132),B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_194,c_20,c_20,c_194,c_3180])).

tff(c_3464,plain,(
    ! [A_132,A_16] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_16))) = k10_relat_1(k6_relat_1(A_132),A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3330])).

tff(c_3499,plain,(
    ! [A_134,A_135] : k1_relat_1(k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_135))) = k10_relat_1(k6_relat_1(A_134),A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3464])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,k10_relat_1(B_21,A_20)),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_809,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k9_relat_1(A_69,k1_relat_1(k5_relat_1(A_69,B_70))),k1_relat_1(B_70))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_24])).

tff(c_843,plain,(
    ! [A_69,A_16] :
      ( r1_tarski(k9_relat_1(A_69,k1_relat_1(k5_relat_1(A_69,k6_relat_1(A_16)))),A_16)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_809])).

tff(c_857,plain,(
    ! [A_69,A_16] :
      ( r1_tarski(k9_relat_1(A_69,k1_relat_1(k5_relat_1(A_69,k6_relat_1(A_16)))),A_16)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_843])).

tff(c_3517,plain,(
    ! [A_134,A_135] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_134),k10_relat_1(k6_relat_1(A_134),A_135)),A_135)
      | ~ v1_funct_1(k6_relat_1(A_134))
      | ~ v1_relat_1(k6_relat_1(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3499,c_857])).

tff(c_3588,plain,(
    ! [A_134,A_135] : r1_tarski(k9_relat_1(k6_relat_1(A_134),k10_relat_1(k6_relat_1(A_134),A_135)),A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_3517])).

tff(c_4194,plain,(
    r1_tarski(k9_relat_1(k6_relat_1('#skF_1'),'#skF_1'),k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4173,c_3588])).

tff(c_4241,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4194])).

tff(c_4243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:31:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.92  
% 5.06/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.93  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.06/1.93  
% 5.06/1.93  %Foreground sorts:
% 5.06/1.93  
% 5.06/1.93  
% 5.06/1.93  %Background operators:
% 5.06/1.93  
% 5.06/1.93  
% 5.06/1.93  %Foreground operators:
% 5.06/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.06/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.06/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.06/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.06/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.93  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.06/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/1.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.06/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/1.93  
% 5.06/1.94  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.06/1.94  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.06/1.94  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.06/1.94  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.06/1.94  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.06/1.94  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.06/1.94  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 5.06/1.94  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 5.06/1.94  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.06/1.94  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 5.06/1.94  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 5.06/1.94  tff(c_26, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.06/1.94  tff(c_20, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.06/1.94  tff(c_16, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.06/1.94  tff(c_14, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.06/1.94  tff(c_51, plain, (![A_26]: (k9_relat_1(A_26, k1_relat_1(A_26))=k2_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.06/1.94  tff(c_60, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=k2_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_51])).
% 5.06/1.94  tff(c_64, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_60])).
% 5.06/1.94  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.06/1.94  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/1.94  tff(c_22, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.06/1.94  tff(c_75, plain, (![A_30]: (k10_relat_1(A_30, k2_relat_1(A_30))=k1_relat_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.94  tff(c_84, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_75])).
% 5.06/1.94  tff(c_88, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_84])).
% 5.06/1.94  tff(c_118, plain, (![B_36, A_37]: (r1_tarski(k9_relat_1(B_36, k10_relat_1(B_36, A_37)), A_37) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.06/1.94  tff(c_121, plain, (![A_16]: (r1_tarski(k9_relat_1(k6_relat_1(A_16), A_16), A_16) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_118])).
% 5.06/1.94  tff(c_126, plain, (![A_16]: (r1_tarski(A_16, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_64, c_121])).
% 5.06/1.94  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.06/1.94  tff(c_98, plain, (![B_32, A_33]: (k5_relat_1(B_32, k6_relat_1(A_33))=B_32 | ~r1_tarski(k2_relat_1(B_32), A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.94  tff(c_101, plain, (![A_16, A_33]: (k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_33))=k6_relat_1(A_16) | ~r1_tarski(A_16, A_33) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_98])).
% 5.06/1.94  tff(c_103, plain, (![A_16, A_33]: (k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_33))=k6_relat_1(A_16) | ~r1_tarski(A_16, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_101])).
% 5.06/1.94  tff(c_127, plain, (![A_38, B_39]: (k10_relat_1(A_38, k1_relat_1(B_39))=k1_relat_1(k5_relat_1(A_38, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.06/1.94  tff(c_147, plain, (![A_38, A_16]: (k1_relat_1(k5_relat_1(A_38, k6_relat_1(A_16)))=k10_relat_1(A_38, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_14, c_127])).
% 5.06/1.94  tff(c_258, plain, (![A_46, A_47]: (k1_relat_1(k5_relat_1(A_46, k6_relat_1(A_47)))=k10_relat_1(A_46, A_47) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_147])).
% 5.06/1.94  tff(c_279, plain, (![A_16, A_33]: (k10_relat_1(k6_relat_1(A_16), A_33)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)) | ~r1_tarski(A_16, A_33))), inference(superposition, [status(thm), theory('equality')], [c_103, c_258])).
% 5.06/1.94  tff(c_285, plain, (![A_16, A_33]: (k10_relat_1(k6_relat_1(A_16), A_33)=A_16 | ~r1_tarski(A_16, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_279])).
% 5.06/1.94  tff(c_411, plain, (![B_53, C_54, A_55]: (k10_relat_1(k5_relat_1(B_53, C_54), A_55)=k10_relat_1(B_53, k10_relat_1(C_54, A_55)) | ~v1_relat_1(C_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.06/1.94  tff(c_441, plain, (![A_16, A_33, A_55]: (k10_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_33), A_55))=k10_relat_1(k6_relat_1(A_16), A_55) | ~v1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(k6_relat_1(A_16)) | ~r1_tarski(A_16, A_33))), inference(superposition, [status(thm), theory('equality')], [c_103, c_411])).
% 5.06/1.94  tff(c_1718, plain, (![A_99, A_100, A_101]: (k10_relat_1(k6_relat_1(A_99), k10_relat_1(k6_relat_1(A_100), A_101))=k10_relat_1(k6_relat_1(A_99), A_101) | ~r1_tarski(A_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_441])).
% 5.06/1.94  tff(c_1871, plain, (![A_102, A_103, A_104]: (k10_relat_1(k6_relat_1(A_102), A_103)=A_102 | ~r1_tarski(A_102, k10_relat_1(k6_relat_1(A_104), A_103)) | ~r1_tarski(A_102, A_104))), inference(superposition, [status(thm), theory('equality')], [c_1718, c_285])).
% 5.06/1.94  tff(c_2413, plain, (![A_116, A_117, A_118]: (k10_relat_1(k6_relat_1(A_116), A_117)=A_116 | ~r1_tarski(A_116, A_118) | ~r1_tarski(A_116, A_118) | ~r1_tarski(A_118, A_117))), inference(superposition, [status(thm), theory('equality')], [c_285, c_1871])).
% 5.06/1.94  tff(c_2443, plain, (![A_117]: (k10_relat_1(k6_relat_1('#skF_1'), A_117)='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), A_117))), inference(resolution, [status(thm)], [c_28, c_2413])).
% 5.06/1.94  tff(c_2465, plain, (![A_119]: (k10_relat_1(k6_relat_1('#skF_1'), A_119)='#skF_1' | ~r1_tarski(k1_relat_1('#skF_2'), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2443])).
% 5.06/1.94  tff(c_2485, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_126, c_2465])).
% 5.06/1.94  tff(c_12, plain, (![A_13, B_15]: (k10_relat_1(A_13, k1_relat_1(B_15))=k1_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.06/1.94  tff(c_2530, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2485, c_12])).
% 5.06/1.94  tff(c_2568, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_2530])).
% 5.06/1.94  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.06/1.94  tff(c_222, plain, (![B_43, C_44, A_45]: (k9_relat_1(k5_relat_1(B_43, C_44), A_45)=k9_relat_1(C_44, k9_relat_1(B_43, A_45)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.06/1.94  tff(c_249, plain, (![C_44, B_43]: (k9_relat_1(C_44, k9_relat_1(B_43, k1_relat_1(k5_relat_1(B_43, C_44))))=k2_relat_1(k5_relat_1(B_43, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43) | ~v1_relat_1(k5_relat_1(B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_222])).
% 5.06/1.94  tff(c_2585, plain, (k9_relat_1('#skF_2', k9_relat_1(k6_relat_1('#skF_1'), '#skF_1'))=k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2568, c_249])).
% 5.06/1.94  tff(c_2621, plain, (k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_64, c_2585])).
% 5.06/1.94  tff(c_4069, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_2621])).
% 5.06/1.94  tff(c_4072, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_4069])).
% 5.06/1.94  tff(c_4076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_4072])).
% 5.06/1.94  tff(c_4078, plain, (v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_2621])).
% 5.06/1.94  tff(c_4077, plain, (k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))=k9_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_2621])).
% 5.06/1.94  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.94  tff(c_445, plain, (![B_53, C_54]: (k10_relat_1(B_53, k10_relat_1(C_54, k2_relat_1(k5_relat_1(B_53, C_54))))=k1_relat_1(k5_relat_1(B_53, C_54)) | ~v1_relat_1(C_54) | ~v1_relat_1(B_53) | ~v1_relat_1(k5_relat_1(B_53, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_411])).
% 5.06/1.94  tff(c_4144, plain, (k10_relat_1(k6_relat_1('#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4077, c_445])).
% 5.06/1.94  tff(c_4173, plain, (k10_relat_1(k6_relat_1('#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4078, c_20, c_30, c_2568, c_4144])).
% 5.06/1.94  tff(c_156, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_64, c_121])).
% 5.06/1.94  tff(c_18, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.06/1.94  tff(c_162, plain, (![B_41]: (k5_relat_1(B_41, k6_relat_1(k2_relat_1(B_41)))=B_41 | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_156, c_18])).
% 5.06/1.94  tff(c_182, plain, (![A_16]: (k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_16))=k6_relat_1(A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_162])).
% 5.06/1.94  tff(c_194, plain, (![A_16]: (k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_16))=k6_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_182])).
% 5.06/1.94  tff(c_3107, plain, (![B_129, C_130, B_131]: (k10_relat_1(B_129, k10_relat_1(C_130, k1_relat_1(B_131)))=k1_relat_1(k5_relat_1(k5_relat_1(B_129, C_130), B_131)) | ~v1_relat_1(C_130) | ~v1_relat_1(B_129) | ~v1_relat_1(B_131) | ~v1_relat_1(k5_relat_1(B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_411])).
% 5.06/1.94  tff(c_431, plain, (![A_16, A_55]: (k10_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_16), A_55))=k10_relat_1(k6_relat_1(A_16), A_55) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_411])).
% 5.06/1.94  tff(c_449, plain, (![A_16, A_55]: (k10_relat_1(k6_relat_1(A_16), k10_relat_1(k6_relat_1(A_16), A_55))=k10_relat_1(k6_relat_1(A_16), A_55))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_431])).
% 5.06/1.94  tff(c_3180, plain, (![A_16, B_131]: (k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_16)), B_131))=k10_relat_1(k6_relat_1(A_16), k1_relat_1(B_131)) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_131) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_16), k6_relat_1(A_16))))), inference(superposition, [status(thm), theory('equality')], [c_3107, c_449])).
% 5.06/1.94  tff(c_3330, plain, (![A_132, B_133]: (k10_relat_1(k6_relat_1(A_132), k1_relat_1(B_133))=k1_relat_1(k5_relat_1(k6_relat_1(A_132), B_133)) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_194, c_20, c_20, c_194, c_3180])).
% 5.06/1.94  tff(c_3464, plain, (![A_132, A_16]: (k1_relat_1(k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_16)))=k10_relat_1(k6_relat_1(A_132), A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3330])).
% 5.06/1.94  tff(c_3499, plain, (![A_134, A_135]: (k1_relat_1(k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_135)))=k10_relat_1(k6_relat_1(A_134), A_135))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3464])).
% 5.06/1.94  tff(c_24, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, k10_relat_1(B_21, A_20)), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.06/1.94  tff(c_809, plain, (![A_69, B_70]: (r1_tarski(k9_relat_1(A_69, k1_relat_1(k5_relat_1(A_69, B_70))), k1_relat_1(B_70)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_127, c_24])).
% 5.06/1.94  tff(c_843, plain, (![A_69, A_16]: (r1_tarski(k9_relat_1(A_69, k1_relat_1(k5_relat_1(A_69, k6_relat_1(A_16)))), A_16) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_14, c_809])).
% 5.06/1.94  tff(c_857, plain, (![A_69, A_16]: (r1_tarski(k9_relat_1(A_69, k1_relat_1(k5_relat_1(A_69, k6_relat_1(A_16)))), A_16) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_843])).
% 5.06/1.94  tff(c_3517, plain, (![A_134, A_135]: (r1_tarski(k9_relat_1(k6_relat_1(A_134), k10_relat_1(k6_relat_1(A_134), A_135)), A_135) | ~v1_funct_1(k6_relat_1(A_134)) | ~v1_relat_1(k6_relat_1(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_3499, c_857])).
% 5.06/1.94  tff(c_3588, plain, (![A_134, A_135]: (r1_tarski(k9_relat_1(k6_relat_1(A_134), k10_relat_1(k6_relat_1(A_134), A_135)), A_135))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_3517])).
% 5.06/1.94  tff(c_4194, plain, (r1_tarski(k9_relat_1(k6_relat_1('#skF_1'), '#skF_1'), k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4173, c_3588])).
% 5.06/1.94  tff(c_4241, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4194])).
% 5.06/1.94  tff(c_4243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4241])).
% 5.06/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.94  
% 5.06/1.94  Inference rules
% 5.06/1.94  ----------------------
% 5.06/1.94  #Ref     : 0
% 5.06/1.94  #Sup     : 913
% 5.06/1.94  #Fact    : 0
% 5.06/1.94  #Define  : 0
% 5.06/1.94  #Split   : 1
% 5.06/1.94  #Chain   : 0
% 5.06/1.94  #Close   : 0
% 5.06/1.94  
% 5.06/1.95  Ordering : KBO
% 5.06/1.95  
% 5.06/1.95  Simplification rules
% 5.06/1.95  ----------------------
% 5.06/1.95  #Subsume      : 139
% 5.06/1.95  #Demod        : 1140
% 5.06/1.95  #Tautology    : 341
% 5.06/1.95  #SimpNegUnit  : 1
% 5.06/1.95  #BackRed      : 0
% 5.06/1.95  
% 5.06/1.95  #Partial instantiations: 0
% 5.06/1.95  #Strategies tried      : 1
% 5.06/1.95  
% 5.06/1.95  Timing (in seconds)
% 5.06/1.95  ----------------------
% 5.06/1.95  Preprocessing        : 0.31
% 5.06/1.95  Parsing              : 0.17
% 5.06/1.95  CNF conversion       : 0.02
% 5.06/1.95  Main loop            : 0.84
% 5.06/1.95  Inferencing          : 0.28
% 5.06/1.95  Reduction            : 0.32
% 5.06/1.95  Demodulation         : 0.25
% 5.06/1.95  BG Simplification    : 0.04
% 5.06/1.95  Subsumption          : 0.15
% 5.06/1.95  Abstraction          : 0.05
% 5.06/1.95  MUC search           : 0.00
% 5.06/1.95  Cooper               : 0.00
% 5.06/1.95  Total                : 1.19
% 5.06/1.95  Index Insertion      : 0.00
% 5.06/1.95  Index Deletion       : 0.00
% 5.06/1.95  Index Matching       : 0.00
% 5.06/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
