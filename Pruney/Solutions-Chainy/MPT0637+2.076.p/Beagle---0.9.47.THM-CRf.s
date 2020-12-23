%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  126 (2704 expanded)
%              Number of leaves         :   31 ( 957 expanded)
%              Depth                    :   22
%              Number of atoms          :  205 (4827 expanded)
%              Number of equality atoms :   94 (1719 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_67,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_30,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k5_relat_1(B_15,k6_relat_1(A_14)) = k8_relat_1(A_14,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_24] : k4_relat_1(k6_relat_1(A_24)) = k6_relat_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_519,plain,(
    ! [B_72,A_73] :
      ( k5_relat_1(k4_relat_1(B_72),k4_relat_1(A_73)) = k4_relat_1(k5_relat_1(A_73,B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_531,plain,(
    ! [A_24,A_73] :
      ( k5_relat_1(k6_relat_1(A_24),k4_relat_1(A_73)) = k4_relat_1(k5_relat_1(A_73,k6_relat_1(A_24)))
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_519])).

tff(c_541,plain,(
    ! [A_74,A_75] :
      ( k5_relat_1(k6_relat_1(A_74),k4_relat_1(A_75)) = k4_relat_1(k5_relat_1(A_75,k6_relat_1(A_74)))
      | ~ v1_relat_1(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_531])).

tff(c_553,plain,(
    ! [A_24,A_74] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_24),k6_relat_1(A_74))) = k5_relat_1(k6_relat_1(A_74),k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_541])).

tff(c_577,plain,(
    ! [A_78,A_79] : k4_relat_1(k5_relat_1(k6_relat_1(A_78),k6_relat_1(A_79))) = k5_relat_1(k6_relat_1(A_79),k6_relat_1(A_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_553])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_547,plain,(
    ! [A_75,A_74] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_75,k6_relat_1(A_74))))
      | ~ v1_relat_1(k4_relat_1(A_75))
      | ~ v1_relat_1(k6_relat_1(A_74))
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_10])).

tff(c_556,plain,(
    ! [A_75,A_74] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_75,k6_relat_1(A_74))))
      | ~ v1_relat_1(k4_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_547])).

tff(c_583,plain,(
    ! [A_79,A_78] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_79),k6_relat_1(A_78)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_78)))
      | ~ v1_relat_1(k6_relat_1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_556])).

tff(c_675,plain,(
    ! [A_83,A_84] : v1_relat_1(k5_relat_1(k6_relat_1(A_83),k6_relat_1(A_84))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_24,c_583])).

tff(c_681,plain,(
    ! [A_14,A_83] :
      ( v1_relat_1(k8_relat_1(A_14,k6_relat_1(A_83)))
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_675])).

tff(c_690,plain,(
    ! [A_14,A_83] : v1_relat_1(k8_relat_1(A_14,k6_relat_1(A_83))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_681])).

tff(c_22,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,(
    ! [A_40] :
      ( k5_relat_1(A_40,k6_relat_1(k2_relat_1(A_40))) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_92,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_96,plain,(
    ! [A_23] : k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_126,plain,(
    ! [B_47,A_48] :
      ( k5_relat_1(B_47,k6_relat_1(A_48)) = k8_relat_1(A_48,B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_23] :
      ( k8_relat_1(A_23,k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_126])).

tff(c_162,plain,(
    ! [A_23] : k8_relat_1(A_23,k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_149])).

tff(c_164,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(k2_relat_1(B_51),A_52) = k2_relat_1(k8_relat_1(A_52,B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [A_52,A_23] :
      ( k2_relat_1(k8_relat_1(A_52,k6_relat_1(A_23))) = k3_xboole_0(A_23,A_52)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_164])).

tff(c_196,plain,(
    ! [A_54,A_55] : k2_relat_1(k8_relat_1(A_54,k6_relat_1(A_55))) = k3_xboole_0(A_55,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_176])).

tff(c_211,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = k2_relat_1(k6_relat_1(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_196])).

tff(c_214,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_211])).

tff(c_180,plain,(
    ! [A_52,A_23] : k2_relat_1(k8_relat_1(A_52,k6_relat_1(A_23))) = k3_xboole_0(A_23,A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_176])).

tff(c_602,plain,(
    ! [A_14,A_78] :
      ( k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_78)) = k4_relat_1(k8_relat_1(A_14,k6_relat_1(A_78)))
      | ~ v1_relat_1(k6_relat_1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_577])).

tff(c_711,plain,(
    ! [A_87,A_88] : k5_relat_1(k6_relat_1(A_87),k6_relat_1(A_88)) = k4_relat_1(k8_relat_1(A_87,k6_relat_1(A_88))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_602])).

tff(c_741,plain,(
    ! [A_87,A_14] :
      ( k4_relat_1(k8_relat_1(A_87,k6_relat_1(A_14))) = k8_relat_1(A_14,k6_relat_1(A_87))
      | ~ v1_relat_1(k6_relat_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_711])).

tff(c_763,plain,(
    ! [A_87,A_14] : k4_relat_1(k8_relat_1(A_87,k6_relat_1(A_14))) = k8_relat_1(A_14,k6_relat_1(A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_741])).

tff(c_616,plain,(
    ! [A_14,A_78] : k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_78)) = k4_relat_1(k8_relat_1(A_14,k6_relat_1(A_78))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_602])).

tff(c_843,plain,(
    ! [A_14,A_78] : k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_78)) = k8_relat_1(A_78,k6_relat_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_616])).

tff(c_28,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k6_relat_1(k2_relat_1(A_27))) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    ! [B_47] :
      ( k8_relat_1(k2_relat_1(B_47),B_47) = B_47
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_28])).

tff(c_890,plain,(
    ! [A_97,A_98] : k5_relat_1(k6_relat_1(A_97),k6_relat_1(A_98)) = k8_relat_1(A_98,k6_relat_1(A_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_616])).

tff(c_16,plain,(
    ! [A_16,B_17,C_19] :
      ( k8_relat_1(A_16,k5_relat_1(B_17,C_19)) = k5_relat_1(B_17,k8_relat_1(A_16,C_19))
      | ~ v1_relat_1(C_19)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_896,plain,(
    ! [A_97,A_16,A_98] :
      ( k5_relat_1(k6_relat_1(A_97),k8_relat_1(A_16,k6_relat_1(A_98))) = k8_relat_1(A_16,k8_relat_1(A_98,k6_relat_1(A_97)))
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_16])).

tff(c_3031,plain,(
    ! [A_168,A_169,A_170] : k5_relat_1(k6_relat_1(A_168),k8_relat_1(A_169,k6_relat_1(A_170))) = k8_relat_1(A_169,k8_relat_1(A_170,k6_relat_1(A_168))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_896])).

tff(c_3089,plain,(
    ! [A_170,A_168] :
      ( k8_relat_1(k2_relat_1(k6_relat_1(A_170)),k8_relat_1(A_170,k6_relat_1(A_168))) = k5_relat_1(k6_relat_1(A_168),k6_relat_1(A_170))
      | ~ v1_relat_1(k6_relat_1(A_170))
      | ~ v1_relat_1(k6_relat_1(A_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_3031])).

tff(c_3379,plain,(
    ! [A_178,A_179] : k8_relat_1(A_178,k8_relat_1(A_178,k6_relat_1(A_179))) = k8_relat_1(A_178,k6_relat_1(A_179)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_843,c_22,c_3089])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(k2_relat_1(B_13),A_12) = k2_relat_1(k8_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_285,plain,(
    ! [B_61,A_62] :
      ( k5_relat_1(B_61,k6_relat_1(A_62)) = B_61
      | ~ r1_tarski(k2_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_298,plain,(
    ! [A_23,A_62] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_62)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_62)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_285])).

tff(c_362,plain,(
    ! [A_64,A_65] :
      ( k5_relat_1(k6_relat_1(A_64),k6_relat_1(A_65)) = k6_relat_1(A_64)
      | ~ r1_tarski(A_64,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_298])).

tff(c_389,plain,(
    ! [A_14,A_64] :
      ( k8_relat_1(A_14,k6_relat_1(A_64)) = k6_relat_1(A_64)
      | ~ r1_tarski(A_64,A_14)
      | ~ v1_relat_1(k6_relat_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_362])).

tff(c_418,plain,(
    ! [A_66,A_67] :
      ( k8_relat_1(A_66,k6_relat_1(A_67)) = k6_relat_1(A_67)
      | ~ r1_tarski(A_67,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_389])).

tff(c_438,plain,(
    ! [A_67,A_66] :
      ( k3_xboole_0(A_67,A_66) = k2_relat_1(k6_relat_1(A_67))
      | ~ r1_tarski(A_67,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_180])).

tff(c_477,plain,(
    ! [A_68,A_69] :
      ( k3_xboole_0(A_68,A_69) = A_68
      | ~ r1_tarski(A_68,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_438])).

tff(c_491,plain,(
    ! [A_70,B_71] : k3_xboole_0(k3_xboole_0(A_70,B_71),A_70) = k3_xboole_0(A_70,B_71) ),
    inference(resolution,[status(thm)],[c_2,c_477])).

tff(c_512,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_12,B_13)),k2_relat_1(B_13)) = k3_xboole_0(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_491])).

tff(c_3404,plain,(
    ! [A_178,A_179] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_178,k6_relat_1(A_179))),k2_relat_1(k8_relat_1(A_178,k6_relat_1(A_179)))) = k3_xboole_0(k2_relat_1(k8_relat_1(A_178,k6_relat_1(A_179))),A_178)
      | ~ v1_relat_1(k8_relat_1(A_178,k6_relat_1(A_179))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3379,c_512])).

tff(c_3474,plain,(
    ! [A_179,A_178] : k3_xboole_0(k3_xboole_0(A_179,A_178),A_178) = k3_xboole_0(A_179,A_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_214,c_180,c_180,c_180,c_3404])).

tff(c_170,plain,(
    ! [A_52,B_51] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_52,B_51)),k2_relat_1(B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_2])).

tff(c_8312,plain,(
    ! [A_263,B_264] :
      ( k5_relat_1(k8_relat_1(A_263,B_264),k6_relat_1(k2_relat_1(B_264))) = k8_relat_1(A_263,B_264)
      | ~ v1_relat_1(k8_relat_1(A_263,B_264))
      | ~ v1_relat_1(B_264) ) ),
    inference(resolution,[status(thm)],[c_170,c_285])).

tff(c_8410,plain,(
    ! [A_263,A_23] :
      ( k5_relat_1(k8_relat_1(A_263,k6_relat_1(A_23)),k6_relat_1(A_23)) = k8_relat_1(A_263,k6_relat_1(A_23))
      | ~ v1_relat_1(k8_relat_1(A_263,k6_relat_1(A_23)))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8312])).

tff(c_8447,plain,(
    ! [A_265,A_266] : k5_relat_1(k8_relat_1(A_265,k6_relat_1(A_266)),k6_relat_1(A_266)) = k8_relat_1(A_265,k6_relat_1(A_266)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_690,c_8410])).

tff(c_8475,plain,(
    ! [A_266,A_265] :
      ( k8_relat_1(A_266,k8_relat_1(A_265,k6_relat_1(A_266))) = k8_relat_1(A_265,k6_relat_1(A_266))
      | ~ v1_relat_1(k8_relat_1(A_265,k6_relat_1(A_266))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8447,c_14])).

tff(c_8546,plain,(
    ! [A_266,A_265] : k8_relat_1(A_266,k8_relat_1(A_265,k6_relat_1(A_266))) = k8_relat_1(A_265,k6_relat_1(A_266)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_8475])).

tff(c_620,plain,(
    ! [A_80,B_81,C_82] :
      ( k8_relat_1(A_80,k5_relat_1(B_81,C_82)) = k5_relat_1(B_81,k8_relat_1(A_80,C_82))
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_656,plain,(
    ! [B_15,A_80,A_14] :
      ( k5_relat_1(B_15,k8_relat_1(A_80,k6_relat_1(A_14))) = k8_relat_1(A_80,k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_620])).

tff(c_670,plain,(
    ! [B_15,A_80,A_14] :
      ( k5_relat_1(B_15,k8_relat_1(A_80,k6_relat_1(A_14))) = k8_relat_1(A_80,k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_656])).

tff(c_534,plain,(
    ! [B_72,A_24] :
      ( k5_relat_1(k4_relat_1(B_72),k6_relat_1(A_24)) = k4_relat_1(k5_relat_1(k6_relat_1(A_24),B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_519])).

tff(c_781,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(k4_relat_1(B_91),k6_relat_1(A_92)) = k4_relat_1(k5_relat_1(k6_relat_1(A_92),B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_534])).

tff(c_6278,plain,(
    ! [A_239,B_240] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_239),B_240)) = k8_relat_1(A_239,k4_relat_1(B_240))
      | ~ v1_relat_1(k4_relat_1(B_240))
      | ~ v1_relat_1(B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_14])).

tff(c_6336,plain,(
    ! [A_239,A_80,A_14] :
      ( k8_relat_1(A_239,k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))) = k4_relat_1(k8_relat_1(A_80,k8_relat_1(A_14,k6_relat_1(A_239))))
      | ~ v1_relat_1(k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14))))
      | ~ v1_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))
      | ~ v1_relat_1(k6_relat_1(A_239)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_6278])).

tff(c_14595,plain,(
    ! [A_336,A_337,A_338] : k4_relat_1(k8_relat_1(A_336,k8_relat_1(A_337,k6_relat_1(A_338)))) = k8_relat_1(A_338,k8_relat_1(A_337,k6_relat_1(A_336))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_690,c_690,c_763,c_763,c_6336])).

tff(c_14659,plain,(
    ! [A_266,A_265] : k8_relat_1(A_266,k8_relat_1(A_265,k6_relat_1(A_266))) = k4_relat_1(k8_relat_1(A_265,k6_relat_1(A_266))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8546,c_14595])).

tff(c_14774,plain,(
    ! [A_340,A_339] : k8_relat_1(A_340,k6_relat_1(A_339)) = k8_relat_1(A_339,k6_relat_1(A_340)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8546,c_763,c_14659])).

tff(c_15030,plain,(
    ! [A_339,A_340] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_339,k6_relat_1(A_340))),k2_relat_1(k6_relat_1(A_339))) = k3_xboole_0(k2_relat_1(k6_relat_1(A_339)),A_340)
      | ~ v1_relat_1(k6_relat_1(A_339)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14774,c_512])).

tff(c_15316,plain,(
    ! [A_340,A_339] : k3_xboole_0(A_340,A_339) = k3_xboole_0(A_339,A_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3474,c_180,c_22,c_22,c_15030])).

tff(c_15569,plain,(
    ! [A_347,A_346] : k3_xboole_0(A_347,A_346) = k3_xboole_0(A_346,A_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3474,c_180,c_22,c_22,c_15030])).

tff(c_490,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_477])).

tff(c_930,plain,(
    ! [A_97,A_16,A_98] : k5_relat_1(k6_relat_1(A_97),k8_relat_1(A_16,k6_relat_1(A_98))) = k8_relat_1(A_16,k8_relat_1(A_98,k6_relat_1(A_97))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_896])).

tff(c_302,plain,(
    ! [A_23,A_62] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_62)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_298])).

tff(c_649,plain,(
    ! [A_23,A_80,A_62] :
      ( k5_relat_1(k6_relat_1(A_23),k8_relat_1(A_80,k6_relat_1(A_62))) = k8_relat_1(A_80,k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_620])).

tff(c_668,plain,(
    ! [A_23,A_80,A_62] :
      ( k5_relat_1(k6_relat_1(A_23),k8_relat_1(A_80,k6_relat_1(A_62))) = k8_relat_1(A_80,k6_relat_1(A_23))
      | ~ r1_tarski(A_23,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_649])).

tff(c_4315,plain,(
    ! [A_199,A_200,A_201] :
      ( k8_relat_1(A_199,k8_relat_1(A_200,k6_relat_1(A_201))) = k8_relat_1(A_199,k6_relat_1(A_201))
      | ~ r1_tarski(A_201,A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_668])).

tff(c_4459,plain,(
    ! [A_200,A_201] :
      ( k8_relat_1(k2_relat_1(k8_relat_1(A_200,k6_relat_1(A_201))),k6_relat_1(A_201)) = k8_relat_1(A_200,k6_relat_1(A_201))
      | ~ r1_tarski(A_201,A_200)
      | ~ v1_relat_1(k8_relat_1(A_200,k6_relat_1(A_201)))
      | ~ v1_relat_1(k8_relat_1(A_200,k6_relat_1(A_201))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_4315])).

tff(c_5873,plain,(
    ! [A_235,A_236] :
      ( k8_relat_1(k3_xboole_0(A_235,A_236),k6_relat_1(A_235)) = k8_relat_1(A_236,k6_relat_1(A_235))
      | ~ r1_tarski(A_235,A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_180,c_4459])).

tff(c_6010,plain,(
    ! [A_1,B_2] :
      ( k8_relat_1(k3_xboole_0(A_1,B_2),k6_relat_1(k3_xboole_0(A_1,B_2))) = k8_relat_1(A_1,k6_relat_1(k3_xboole_0(A_1,B_2)))
      | ~ r1_tarski(k3_xboole_0(A_1,B_2),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_5873])).

tff(c_6069,plain,(
    ! [A_1,B_2] : k8_relat_1(A_1,k6_relat_1(k3_xboole_0(A_1,B_2))) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_162,c_6010])).

tff(c_15746,plain,(
    ! [A_346,A_347] : k8_relat_1(A_346,k6_relat_1(k3_xboole_0(A_347,A_346))) = k6_relat_1(k3_xboole_0(A_346,A_347)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15569,c_6069])).

tff(c_2741,plain,(
    ! [B_163] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(B_163))),B_163)) = k4_relat_1(B_163)
      | ~ v1_relat_1(k4_relat_1(B_163))
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_28])).

tff(c_2785,plain,(
    ! [A_80,A_14] :
      ( k4_relat_1(k8_relat_1(A_80,k8_relat_1(A_14,k6_relat_1(k2_relat_1(k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))))))) = k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))
      | ~ v1_relat_1(k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14))))
      | ~ v1_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k8_relat_1(A_80,k6_relat_1(A_14)))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_2741])).

tff(c_2811,plain,(
    ! [A_80,A_14] : k4_relat_1(k8_relat_1(A_80,k8_relat_1(A_14,k6_relat_1(k3_xboole_0(A_80,A_14))))) = k8_relat_1(A_14,k6_relat_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_690,c_690,c_763,c_763,c_180,c_763,c_2785])).

tff(c_23392,plain,(
    ! [A_80,A_14] : k4_relat_1(k6_relat_1(k3_xboole_0(A_80,A_14))) = k8_relat_1(A_14,k6_relat_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15746,c_15746,c_2811])).

tff(c_23393,plain,(
    ! [A_14,A_80] : k8_relat_1(A_14,k6_relat_1(A_80)) = k6_relat_1(k3_xboole_0(A_80,A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_23392])).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_34])).

tff(c_159,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_139])).

tff(c_23769,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23393,c_159])).

tff(c_23786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15316,c_23769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:48:35 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.83  
% 9.55/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.83  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.63/3.83  
% 9.63/3.83  %Foreground sorts:
% 9.63/3.83  
% 9.63/3.83  
% 9.63/3.83  %Background operators:
% 9.63/3.83  
% 9.63/3.83  
% 9.63/3.83  %Foreground operators:
% 9.63/3.83  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.63/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.63/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.63/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/3.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.63/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.63/3.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.63/3.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.63/3.83  tff('#skF_2', type, '#skF_2': $i).
% 9.63/3.83  tff('#skF_1', type, '#skF_1': $i).
% 9.63/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.63/3.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.63/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/3.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.63/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.63/3.83  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.63/3.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.63/3.83  
% 9.73/3.86  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 9.73/3.86  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 9.73/3.86  tff(f_67, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 9.73/3.86  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 9.73/3.86  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.73/3.86  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.73/3.86  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.73/3.86  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 9.73/3.86  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 9.73/3.86  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.73/3.86  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 9.73/3.86  tff(f_84, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 9.73/3.86  tff(c_30, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.73/3.86  tff(c_14, plain, (![B_15, A_14]: (k5_relat_1(B_15, k6_relat_1(A_14))=k8_relat_1(A_14, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.73/3.86  tff(c_24, plain, (![A_24]: (k4_relat_1(k6_relat_1(A_24))=k6_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.73/3.86  tff(c_519, plain, (![B_72, A_73]: (k5_relat_1(k4_relat_1(B_72), k4_relat_1(A_73))=k4_relat_1(k5_relat_1(A_73, B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.73/3.86  tff(c_531, plain, (![A_24, A_73]: (k5_relat_1(k6_relat_1(A_24), k4_relat_1(A_73))=k4_relat_1(k5_relat_1(A_73, k6_relat_1(A_24))) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_519])).
% 9.73/3.86  tff(c_541, plain, (![A_74, A_75]: (k5_relat_1(k6_relat_1(A_74), k4_relat_1(A_75))=k4_relat_1(k5_relat_1(A_75, k6_relat_1(A_74))) | ~v1_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_531])).
% 9.73/3.86  tff(c_553, plain, (![A_24, A_74]: (k4_relat_1(k5_relat_1(k6_relat_1(A_24), k6_relat_1(A_74)))=k5_relat_1(k6_relat_1(A_74), k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_541])).
% 9.73/3.86  tff(c_577, plain, (![A_78, A_79]: (k4_relat_1(k5_relat_1(k6_relat_1(A_78), k6_relat_1(A_79)))=k5_relat_1(k6_relat_1(A_79), k6_relat_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_553])).
% 9.73/3.86  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.73/3.86  tff(c_547, plain, (![A_75, A_74]: (v1_relat_1(k4_relat_1(k5_relat_1(A_75, k6_relat_1(A_74)))) | ~v1_relat_1(k4_relat_1(A_75)) | ~v1_relat_1(k6_relat_1(A_74)) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_541, c_10])).
% 9.73/3.86  tff(c_556, plain, (![A_75, A_74]: (v1_relat_1(k4_relat_1(k5_relat_1(A_75, k6_relat_1(A_74)))) | ~v1_relat_1(k4_relat_1(A_75)) | ~v1_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_547])).
% 9.73/3.86  tff(c_583, plain, (![A_79, A_78]: (v1_relat_1(k5_relat_1(k6_relat_1(A_79), k6_relat_1(A_78))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_78))) | ~v1_relat_1(k6_relat_1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_556])).
% 9.73/3.86  tff(c_675, plain, (![A_83, A_84]: (v1_relat_1(k5_relat_1(k6_relat_1(A_83), k6_relat_1(A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_24, c_583])).
% 9.73/3.86  tff(c_681, plain, (![A_14, A_83]: (v1_relat_1(k8_relat_1(A_14, k6_relat_1(A_83))) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_675])).
% 9.73/3.86  tff(c_690, plain, (![A_14, A_83]: (v1_relat_1(k8_relat_1(A_14, k6_relat_1(A_83))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_681])).
% 9.73/3.86  tff(c_22, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.73/3.86  tff(c_83, plain, (![A_40]: (k5_relat_1(A_40, k6_relat_1(k2_relat_1(A_40)))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.73/3.86  tff(c_92, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_23))=k6_relat_1(A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_83])).
% 9.73/3.86  tff(c_96, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_23))=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 9.73/3.86  tff(c_126, plain, (![B_47, A_48]: (k5_relat_1(B_47, k6_relat_1(A_48))=k8_relat_1(A_48, B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.73/3.86  tff(c_149, plain, (![A_23]: (k8_relat_1(A_23, k6_relat_1(A_23))=k6_relat_1(A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_126])).
% 9.73/3.86  tff(c_162, plain, (![A_23]: (k8_relat_1(A_23, k6_relat_1(A_23))=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_149])).
% 9.73/3.86  tff(c_164, plain, (![B_51, A_52]: (k3_xboole_0(k2_relat_1(B_51), A_52)=k2_relat_1(k8_relat_1(A_52, B_51)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.73/3.86  tff(c_176, plain, (![A_52, A_23]: (k2_relat_1(k8_relat_1(A_52, k6_relat_1(A_23)))=k3_xboole_0(A_23, A_52) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_164])).
% 9.73/3.86  tff(c_196, plain, (![A_54, A_55]: (k2_relat_1(k8_relat_1(A_54, k6_relat_1(A_55)))=k3_xboole_0(A_55, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_176])).
% 9.73/3.86  tff(c_211, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=k2_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_196])).
% 9.73/3.86  tff(c_214, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_211])).
% 9.73/3.86  tff(c_180, plain, (![A_52, A_23]: (k2_relat_1(k8_relat_1(A_52, k6_relat_1(A_23)))=k3_xboole_0(A_23, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_176])).
% 9.73/3.86  tff(c_602, plain, (![A_14, A_78]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_78))=k4_relat_1(k8_relat_1(A_14, k6_relat_1(A_78))) | ~v1_relat_1(k6_relat_1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_577])).
% 9.73/3.86  tff(c_711, plain, (![A_87, A_88]: (k5_relat_1(k6_relat_1(A_87), k6_relat_1(A_88))=k4_relat_1(k8_relat_1(A_87, k6_relat_1(A_88))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_602])).
% 9.73/3.86  tff(c_741, plain, (![A_87, A_14]: (k4_relat_1(k8_relat_1(A_87, k6_relat_1(A_14)))=k8_relat_1(A_14, k6_relat_1(A_87)) | ~v1_relat_1(k6_relat_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_711])).
% 9.73/3.86  tff(c_763, plain, (![A_87, A_14]: (k4_relat_1(k8_relat_1(A_87, k6_relat_1(A_14)))=k8_relat_1(A_14, k6_relat_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_741])).
% 9.73/3.86  tff(c_616, plain, (![A_14, A_78]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_78))=k4_relat_1(k8_relat_1(A_14, k6_relat_1(A_78))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_602])).
% 9.73/3.86  tff(c_843, plain, (![A_14, A_78]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_78))=k8_relat_1(A_78, k6_relat_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_763, c_616])).
% 9.73/3.86  tff(c_28, plain, (![A_27]: (k5_relat_1(A_27, k6_relat_1(k2_relat_1(A_27)))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.73/3.86  tff(c_143, plain, (![B_47]: (k8_relat_1(k2_relat_1(B_47), B_47)=B_47 | ~v1_relat_1(B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_126, c_28])).
% 9.73/3.86  tff(c_890, plain, (![A_97, A_98]: (k5_relat_1(k6_relat_1(A_97), k6_relat_1(A_98))=k8_relat_1(A_98, k6_relat_1(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_763, c_616])).
% 9.73/3.86  tff(c_16, plain, (![A_16, B_17, C_19]: (k8_relat_1(A_16, k5_relat_1(B_17, C_19))=k5_relat_1(B_17, k8_relat_1(A_16, C_19)) | ~v1_relat_1(C_19) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.73/3.86  tff(c_896, plain, (![A_97, A_16, A_98]: (k5_relat_1(k6_relat_1(A_97), k8_relat_1(A_16, k6_relat_1(A_98)))=k8_relat_1(A_16, k8_relat_1(A_98, k6_relat_1(A_97))) | ~v1_relat_1(k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_890, c_16])).
% 9.73/3.86  tff(c_3031, plain, (![A_168, A_169, A_170]: (k5_relat_1(k6_relat_1(A_168), k8_relat_1(A_169, k6_relat_1(A_170)))=k8_relat_1(A_169, k8_relat_1(A_170, k6_relat_1(A_168))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_896])).
% 9.73/3.86  tff(c_3089, plain, (![A_170, A_168]: (k8_relat_1(k2_relat_1(k6_relat_1(A_170)), k8_relat_1(A_170, k6_relat_1(A_168)))=k5_relat_1(k6_relat_1(A_168), k6_relat_1(A_170)) | ~v1_relat_1(k6_relat_1(A_170)) | ~v1_relat_1(k6_relat_1(A_170)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_3031])).
% 9.73/3.86  tff(c_3379, plain, (![A_178, A_179]: (k8_relat_1(A_178, k8_relat_1(A_178, k6_relat_1(A_179)))=k8_relat_1(A_178, k6_relat_1(A_179)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_843, c_22, c_3089])).
% 9.73/3.86  tff(c_12, plain, (![B_13, A_12]: (k3_xboole_0(k2_relat_1(B_13), A_12)=k2_relat_1(k8_relat_1(A_12, B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.73/3.86  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.73/3.86  tff(c_285, plain, (![B_61, A_62]: (k5_relat_1(B_61, k6_relat_1(A_62))=B_61 | ~r1_tarski(k2_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.73/3.86  tff(c_298, plain, (![A_23, A_62]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_62))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_62) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_285])).
% 9.73/3.86  tff(c_362, plain, (![A_64, A_65]: (k5_relat_1(k6_relat_1(A_64), k6_relat_1(A_65))=k6_relat_1(A_64) | ~r1_tarski(A_64, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_298])).
% 9.73/3.86  tff(c_389, plain, (![A_14, A_64]: (k8_relat_1(A_14, k6_relat_1(A_64))=k6_relat_1(A_64) | ~r1_tarski(A_64, A_14) | ~v1_relat_1(k6_relat_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_362])).
% 9.73/3.86  tff(c_418, plain, (![A_66, A_67]: (k8_relat_1(A_66, k6_relat_1(A_67))=k6_relat_1(A_67) | ~r1_tarski(A_67, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_389])).
% 9.73/3.86  tff(c_438, plain, (![A_67, A_66]: (k3_xboole_0(A_67, A_66)=k2_relat_1(k6_relat_1(A_67)) | ~r1_tarski(A_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_418, c_180])).
% 9.73/3.86  tff(c_477, plain, (![A_68, A_69]: (k3_xboole_0(A_68, A_69)=A_68 | ~r1_tarski(A_68, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_438])).
% 9.73/3.86  tff(c_491, plain, (![A_70, B_71]: (k3_xboole_0(k3_xboole_0(A_70, B_71), A_70)=k3_xboole_0(A_70, B_71))), inference(resolution, [status(thm)], [c_2, c_477])).
% 9.73/3.86  tff(c_512, plain, (![A_12, B_13]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_12, B_13)), k2_relat_1(B_13))=k3_xboole_0(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_491])).
% 9.73/3.86  tff(c_3404, plain, (![A_178, A_179]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_178, k6_relat_1(A_179))), k2_relat_1(k8_relat_1(A_178, k6_relat_1(A_179))))=k3_xboole_0(k2_relat_1(k8_relat_1(A_178, k6_relat_1(A_179))), A_178) | ~v1_relat_1(k8_relat_1(A_178, k6_relat_1(A_179))))), inference(superposition, [status(thm), theory('equality')], [c_3379, c_512])).
% 9.73/3.86  tff(c_3474, plain, (![A_179, A_178]: (k3_xboole_0(k3_xboole_0(A_179, A_178), A_178)=k3_xboole_0(A_179, A_178))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_214, c_180, c_180, c_180, c_3404])).
% 9.73/3.86  tff(c_170, plain, (![A_52, B_51]: (r1_tarski(k2_relat_1(k8_relat_1(A_52, B_51)), k2_relat_1(B_51)) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_164, c_2])).
% 9.73/3.86  tff(c_8312, plain, (![A_263, B_264]: (k5_relat_1(k8_relat_1(A_263, B_264), k6_relat_1(k2_relat_1(B_264)))=k8_relat_1(A_263, B_264) | ~v1_relat_1(k8_relat_1(A_263, B_264)) | ~v1_relat_1(B_264))), inference(resolution, [status(thm)], [c_170, c_285])).
% 9.73/3.86  tff(c_8410, plain, (![A_263, A_23]: (k5_relat_1(k8_relat_1(A_263, k6_relat_1(A_23)), k6_relat_1(A_23))=k8_relat_1(A_263, k6_relat_1(A_23)) | ~v1_relat_1(k8_relat_1(A_263, k6_relat_1(A_23))) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8312])).
% 9.73/3.86  tff(c_8447, plain, (![A_265, A_266]: (k5_relat_1(k8_relat_1(A_265, k6_relat_1(A_266)), k6_relat_1(A_266))=k8_relat_1(A_265, k6_relat_1(A_266)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_690, c_8410])).
% 9.73/3.86  tff(c_8475, plain, (![A_266, A_265]: (k8_relat_1(A_266, k8_relat_1(A_265, k6_relat_1(A_266)))=k8_relat_1(A_265, k6_relat_1(A_266)) | ~v1_relat_1(k8_relat_1(A_265, k6_relat_1(A_266))))), inference(superposition, [status(thm), theory('equality')], [c_8447, c_14])).
% 9.73/3.86  tff(c_8546, plain, (![A_266, A_265]: (k8_relat_1(A_266, k8_relat_1(A_265, k6_relat_1(A_266)))=k8_relat_1(A_265, k6_relat_1(A_266)))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_8475])).
% 9.73/3.86  tff(c_620, plain, (![A_80, B_81, C_82]: (k8_relat_1(A_80, k5_relat_1(B_81, C_82))=k5_relat_1(B_81, k8_relat_1(A_80, C_82)) | ~v1_relat_1(C_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.73/3.86  tff(c_656, plain, (![B_15, A_80, A_14]: (k5_relat_1(B_15, k8_relat_1(A_80, k6_relat_1(A_14)))=k8_relat_1(A_80, k8_relat_1(A_14, B_15)) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_14, c_620])).
% 9.73/3.86  tff(c_670, plain, (![B_15, A_80, A_14]: (k5_relat_1(B_15, k8_relat_1(A_80, k6_relat_1(A_14)))=k8_relat_1(A_80, k8_relat_1(A_14, B_15)) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_656])).
% 9.73/3.86  tff(c_534, plain, (![B_72, A_24]: (k5_relat_1(k4_relat_1(B_72), k6_relat_1(A_24))=k4_relat_1(k5_relat_1(k6_relat_1(A_24), B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_519])).
% 9.73/3.86  tff(c_781, plain, (![B_91, A_92]: (k5_relat_1(k4_relat_1(B_91), k6_relat_1(A_92))=k4_relat_1(k5_relat_1(k6_relat_1(A_92), B_91)) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_534])).
% 9.73/3.86  tff(c_6278, plain, (![A_239, B_240]: (k4_relat_1(k5_relat_1(k6_relat_1(A_239), B_240))=k8_relat_1(A_239, k4_relat_1(B_240)) | ~v1_relat_1(k4_relat_1(B_240)) | ~v1_relat_1(B_240))), inference(superposition, [status(thm), theory('equality')], [c_781, c_14])).
% 9.73/3.86  tff(c_6336, plain, (![A_239, A_80, A_14]: (k8_relat_1(A_239, k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14))))=k4_relat_1(k8_relat_1(A_80, k8_relat_1(A_14, k6_relat_1(A_239)))) | ~v1_relat_1(k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14)))) | ~v1_relat_1(k8_relat_1(A_80, k6_relat_1(A_14))) | ~v1_relat_1(k6_relat_1(A_239)))), inference(superposition, [status(thm), theory('equality')], [c_670, c_6278])).
% 9.73/3.86  tff(c_14595, plain, (![A_336, A_337, A_338]: (k4_relat_1(k8_relat_1(A_336, k8_relat_1(A_337, k6_relat_1(A_338))))=k8_relat_1(A_338, k8_relat_1(A_337, k6_relat_1(A_336))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_690, c_690, c_763, c_763, c_6336])).
% 9.73/3.86  tff(c_14659, plain, (![A_266, A_265]: (k8_relat_1(A_266, k8_relat_1(A_265, k6_relat_1(A_266)))=k4_relat_1(k8_relat_1(A_265, k6_relat_1(A_266))))), inference(superposition, [status(thm), theory('equality')], [c_8546, c_14595])).
% 9.73/3.86  tff(c_14774, plain, (![A_340, A_339]: (k8_relat_1(A_340, k6_relat_1(A_339))=k8_relat_1(A_339, k6_relat_1(A_340)))), inference(demodulation, [status(thm), theory('equality')], [c_8546, c_763, c_14659])).
% 9.73/3.86  tff(c_15030, plain, (![A_339, A_340]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_339, k6_relat_1(A_340))), k2_relat_1(k6_relat_1(A_339)))=k3_xboole_0(k2_relat_1(k6_relat_1(A_339)), A_340) | ~v1_relat_1(k6_relat_1(A_339)))), inference(superposition, [status(thm), theory('equality')], [c_14774, c_512])).
% 9.73/3.86  tff(c_15316, plain, (![A_340, A_339]: (k3_xboole_0(A_340, A_339)=k3_xboole_0(A_339, A_340))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3474, c_180, c_22, c_22, c_15030])).
% 9.73/3.86  tff(c_15569, plain, (![A_347, A_346]: (k3_xboole_0(A_347, A_346)=k3_xboole_0(A_346, A_347))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3474, c_180, c_22, c_22, c_15030])).
% 9.73/3.86  tff(c_490, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_477])).
% 9.73/3.86  tff(c_930, plain, (![A_97, A_16, A_98]: (k5_relat_1(k6_relat_1(A_97), k8_relat_1(A_16, k6_relat_1(A_98)))=k8_relat_1(A_16, k8_relat_1(A_98, k6_relat_1(A_97))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_896])).
% 9.73/3.86  tff(c_302, plain, (![A_23, A_62]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_62))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_298])).
% 9.73/3.86  tff(c_649, plain, (![A_23, A_80, A_62]: (k5_relat_1(k6_relat_1(A_23), k8_relat_1(A_80, k6_relat_1(A_62)))=k8_relat_1(A_80, k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, A_62))), inference(superposition, [status(thm), theory('equality')], [c_302, c_620])).
% 9.73/3.86  tff(c_668, plain, (![A_23, A_80, A_62]: (k5_relat_1(k6_relat_1(A_23), k8_relat_1(A_80, k6_relat_1(A_62)))=k8_relat_1(A_80, k6_relat_1(A_23)) | ~r1_tarski(A_23, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_649])).
% 9.73/3.86  tff(c_4315, plain, (![A_199, A_200, A_201]: (k8_relat_1(A_199, k8_relat_1(A_200, k6_relat_1(A_201)))=k8_relat_1(A_199, k6_relat_1(A_201)) | ~r1_tarski(A_201, A_200))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_668])).
% 9.73/3.86  tff(c_4459, plain, (![A_200, A_201]: (k8_relat_1(k2_relat_1(k8_relat_1(A_200, k6_relat_1(A_201))), k6_relat_1(A_201))=k8_relat_1(A_200, k6_relat_1(A_201)) | ~r1_tarski(A_201, A_200) | ~v1_relat_1(k8_relat_1(A_200, k6_relat_1(A_201))) | ~v1_relat_1(k8_relat_1(A_200, k6_relat_1(A_201))))), inference(superposition, [status(thm), theory('equality')], [c_143, c_4315])).
% 9.73/3.86  tff(c_5873, plain, (![A_235, A_236]: (k8_relat_1(k3_xboole_0(A_235, A_236), k6_relat_1(A_235))=k8_relat_1(A_236, k6_relat_1(A_235)) | ~r1_tarski(A_235, A_236))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_690, c_180, c_4459])).
% 9.73/3.86  tff(c_6010, plain, (![A_1, B_2]: (k8_relat_1(k3_xboole_0(A_1, B_2), k6_relat_1(k3_xboole_0(A_1, B_2)))=k8_relat_1(A_1, k6_relat_1(k3_xboole_0(A_1, B_2))) | ~r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_490, c_5873])).
% 9.73/3.86  tff(c_6069, plain, (![A_1, B_2]: (k8_relat_1(A_1, k6_relat_1(k3_xboole_0(A_1, B_2)))=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_162, c_6010])).
% 9.73/3.86  tff(c_15746, plain, (![A_346, A_347]: (k8_relat_1(A_346, k6_relat_1(k3_xboole_0(A_347, A_346)))=k6_relat_1(k3_xboole_0(A_346, A_347)))), inference(superposition, [status(thm), theory('equality')], [c_15569, c_6069])).
% 9.73/3.86  tff(c_2741, plain, (![B_163]: (k4_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(B_163))), B_163))=k4_relat_1(B_163) | ~v1_relat_1(k4_relat_1(B_163)) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_781, c_28])).
% 9.73/3.86  tff(c_2785, plain, (![A_80, A_14]: (k4_relat_1(k8_relat_1(A_80, k8_relat_1(A_14, k6_relat_1(k2_relat_1(k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14))))))))=k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14))) | ~v1_relat_1(k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14)))) | ~v1_relat_1(k8_relat_1(A_80, k6_relat_1(A_14))) | ~v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(k8_relat_1(A_80, k6_relat_1(A_14)))))))), inference(superposition, [status(thm), theory('equality')], [c_670, c_2741])).
% 9.73/3.86  tff(c_2811, plain, (![A_80, A_14]: (k4_relat_1(k8_relat_1(A_80, k8_relat_1(A_14, k6_relat_1(k3_xboole_0(A_80, A_14)))))=k8_relat_1(A_14, k6_relat_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_690, c_690, c_763, c_763, c_180, c_763, c_2785])).
% 9.73/3.86  tff(c_23392, plain, (![A_80, A_14]: (k4_relat_1(k6_relat_1(k3_xboole_0(A_80, A_14)))=k8_relat_1(A_14, k6_relat_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_15746, c_15746, c_2811])).
% 9.73/3.86  tff(c_23393, plain, (![A_14, A_80]: (k8_relat_1(A_14, k6_relat_1(A_80))=k6_relat_1(k3_xboole_0(A_80, A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_23392])).
% 9.73/3.86  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.73/3.86  tff(c_139, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_34])).
% 9.73/3.86  tff(c_159, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_139])).
% 9.73/3.86  tff(c_23769, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_23393, c_159])).
% 9.73/3.86  tff(c_23786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15316, c_23769])).
% 9.73/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.73/3.86  
% 9.73/3.86  Inference rules
% 9.73/3.86  ----------------------
% 9.73/3.86  #Ref     : 0
% 9.73/3.86  #Sup     : 5883
% 9.73/3.86  #Fact    : 0
% 9.73/3.86  #Define  : 0
% 9.73/3.86  #Split   : 2
% 9.73/3.86  #Chain   : 0
% 9.73/3.86  #Close   : 0
% 9.73/3.86  
% 9.73/3.86  Ordering : KBO
% 9.73/3.86  
% 9.73/3.86  Simplification rules
% 9.73/3.86  ----------------------
% 9.73/3.86  #Subsume      : 1105
% 9.73/3.86  #Demod        : 7587
% 9.73/3.86  #Tautology    : 2179
% 9.73/3.86  #SimpNegUnit  : 0
% 9.73/3.86  #BackRed      : 53
% 9.73/3.86  
% 9.73/3.86  #Partial instantiations: 0
% 9.73/3.86  #Strategies tried      : 1
% 9.73/3.86  
% 9.73/3.86  Timing (in seconds)
% 9.73/3.86  ----------------------
% 9.73/3.86  Preprocessing        : 0.30
% 9.73/3.86  Parsing              : 0.16
% 9.73/3.86  CNF conversion       : 0.02
% 9.73/3.86  Main loop            : 2.77
% 9.73/3.86  Inferencing          : 0.76
% 9.73/3.86  Reduction            : 1.12
% 9.73/3.86  Demodulation         : 0.92
% 9.73/3.86  BG Simplification    : 0.10
% 9.73/3.86  Subsumption          : 0.63
% 9.73/3.86  Abstraction          : 0.17
% 9.73/3.86  MUC search           : 0.00
% 9.73/3.86  Cooper               : 0.00
% 9.73/3.86  Total                : 3.11
% 9.73/3.86  Index Insertion      : 0.00
% 9.73/3.86  Index Deletion       : 0.00
% 9.73/3.86  Index Matching       : 0.00
% 9.73/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
