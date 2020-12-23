%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 306 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 486 expanded)
%              Number of equality atoms :   61 ( 171 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_66,B_67] : k1_setfam_1(k2_tarski(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [B_70,A_71] : k1_setfam_1(k2_tarski(B_70,A_71)) = k3_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_18,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    ! [B_70,A_71] : k3_xboole_0(B_70,A_71) = k3_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_18])).

tff(c_22,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_49] : k1_relat_1(k6_relat_1(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_371,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(k1_relat_1(B_93),A_94) = k1_relat_1(k7_relat_1(B_93,A_94))
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_394,plain,(
    ! [A_49,A_94] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_49),A_94)) = k3_xboole_0(A_49,A_94)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_371])).

tff(c_398,plain,(
    ! [A_49,A_94] : k1_relat_1(k7_relat_1(k6_relat_1(A_49),A_94)) = k3_xboole_0(A_49,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_394])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( k5_relat_1(k6_relat_1(A_58),B_59) = k7_relat_1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_542,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_108,B_109)),k1_relat_1(A_108))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_551,plain,(
    ! [B_59,A_58] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_59,A_58)),k1_relat_1(k6_relat_1(A_58)))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_542])).

tff(c_578,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_111,A_112)),A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32,c_551])).

tff(c_584,plain,(
    ! [A_49,A_94] :
      ( r1_tarski(k3_xboole_0(A_49,A_94),A_94)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_578])).

tff(c_593,plain,(
    ! [A_113,A_114] : r1_tarski(k3_xboole_0(A_113,A_114),A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_584])).

tff(c_602,plain,(
    ! [B_70,A_71] : r1_tarski(k3_xboole_0(B_70,A_71),B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_593])).

tff(c_590,plain,(
    ! [A_49,A_94] : r1_tarski(k3_xboole_0(A_49,A_94),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_584])).

tff(c_24,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = k8_relat_1(A_37,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_302,plain,(
    ! [A_88,B_89] :
      ( k5_relat_1(k6_relat_1(A_88),B_89) = k7_relat_1(B_89,A_88)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_330,plain,(
    ! [A_37,A_88] :
      ( k8_relat_1(A_37,k6_relat_1(A_88)) = k7_relat_1(k6_relat_1(A_37),A_88)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_302])).

tff(c_436,plain,(
    ! [A_98,A_99] : k8_relat_1(A_98,k6_relat_1(A_99)) = k7_relat_1(k6_relat_1(A_98),A_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_330])).

tff(c_249,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(B_83,k6_relat_1(A_84)) = k8_relat_1(A_84,B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_255,plain,(
    ! [A_84,B_83] :
      ( v1_relat_1(k8_relat_1(A_84,B_83))
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_20])).

tff(c_278,plain,(
    ! [A_84,B_83] :
      ( v1_relat_1(k8_relat_1(A_84,B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_255])).

tff(c_446,plain,(
    ! [A_98,A_99] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_99))
      | ~ v1_relat_1(k6_relat_1(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_278])).

tff(c_456,plain,(
    ! [A_98,A_99] : v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_446])).

tff(c_351,plain,(
    ! [A_37,A_88] : k8_relat_1(A_37,k6_relat_1(A_88)) = k7_relat_1(k6_relat_1(A_37),A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_330])).

tff(c_1778,plain,(
    ! [A_158,B_159,C_160] :
      ( k8_relat_1(A_158,k5_relat_1(B_159,C_160)) = k5_relat_1(B_159,k8_relat_1(A_158,C_160))
      | ~ v1_relat_1(C_160)
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1813,plain,(
    ! [B_38,A_158,A_37] :
      ( k5_relat_1(B_38,k8_relat_1(A_158,k6_relat_1(A_37))) = k8_relat_1(A_158,k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1778])).

tff(c_5450,plain,(
    ! [B_238,A_239,A_240] :
      ( k5_relat_1(B_238,k7_relat_1(k6_relat_1(A_239),A_240)) = k8_relat_1(A_239,k8_relat_1(A_240,B_238))
      | ~ v1_relat_1(B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_351,c_1813])).

tff(c_5475,plain,(
    ! [A_239,A_240,A_58] :
      ( k8_relat_1(A_239,k8_relat_1(A_240,k6_relat_1(A_58))) = k7_relat_1(k7_relat_1(k6_relat_1(A_239),A_240),A_58)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_239),A_240))
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5450,c_46])).

tff(c_5525,plain,(
    ! [A_239,A_240,A_58] : k8_relat_1(A_239,k7_relat_1(k6_relat_1(A_240),A_58)) = k7_relat_1(k7_relat_1(k6_relat_1(A_239),A_240),A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_456,c_351,c_5475])).

tff(c_1810,plain,(
    ! [A_58,A_158,B_59] :
      ( k5_relat_1(k6_relat_1(A_58),k8_relat_1(A_158,B_59)) = k8_relat_1(A_158,k7_relat_1(B_59,A_58))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1778])).

tff(c_4573,plain,(
    ! [A_225,A_226,B_227] :
      ( k5_relat_1(k6_relat_1(A_225),k8_relat_1(A_226,B_227)) = k8_relat_1(A_226,k7_relat_1(B_227,A_225))
      | ~ v1_relat_1(B_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1810])).

tff(c_4617,plain,(
    ! [A_225,A_37,A_88] :
      ( k5_relat_1(k6_relat_1(A_225),k7_relat_1(k6_relat_1(A_37),A_88)) = k8_relat_1(A_37,k7_relat_1(k6_relat_1(A_88),A_225))
      | ~ v1_relat_1(k6_relat_1(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_4573])).

tff(c_4634,plain,(
    ! [A_225,A_37,A_88] : k5_relat_1(k6_relat_1(A_225),k7_relat_1(k6_relat_1(A_37),A_88)) = k8_relat_1(A_37,k7_relat_1(k6_relat_1(A_88),A_225)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4617])).

tff(c_17444,plain,(
    ! [A_225,A_37,A_88] : k5_relat_1(k6_relat_1(A_225),k7_relat_1(k6_relat_1(A_37),A_88)) = k7_relat_1(k7_relat_1(k6_relat_1(A_37),A_88),A_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_4634])).

tff(c_34,plain,(
    ! [A_49] : k2_relat_1(k6_relat_1(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_623,plain,(
    ! [B_117,A_118] :
      ( k5_relat_1(B_117,k6_relat_1(A_118)) = B_117
      | ~ r1_tarski(k2_relat_1(B_117),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_630,plain,(
    ! [A_49,A_118] :
      ( k5_relat_1(k6_relat_1(A_49),k6_relat_1(A_118)) = k6_relat_1(A_49)
      | ~ r1_tarski(A_49,A_118)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_623])).

tff(c_633,plain,(
    ! [A_49,A_118] :
      ( k5_relat_1(k6_relat_1(A_49),k6_relat_1(A_118)) = k6_relat_1(A_49)
      | ~ r1_tarski(A_49,A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_630])).

tff(c_1800,plain,(
    ! [A_49,A_158,A_118] :
      ( k5_relat_1(k6_relat_1(A_49),k8_relat_1(A_158,k6_relat_1(A_118))) = k8_relat_1(A_158,k6_relat_1(A_49))
      | ~ v1_relat_1(k6_relat_1(A_118))
      | ~ v1_relat_1(k6_relat_1(A_49))
      | ~ r1_tarski(A_49,A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_1778])).

tff(c_1823,plain,(
    ! [A_49,A_158,A_118] :
      ( k5_relat_1(k6_relat_1(A_49),k7_relat_1(k6_relat_1(A_158),A_118)) = k7_relat_1(k6_relat_1(A_158),A_49)
      | ~ r1_tarski(A_49,A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_351,c_351,c_1800])).

tff(c_23138,plain,(
    ! [A_591,A_592,A_593] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_591),A_592),A_593) = k7_relat_1(k6_relat_1(A_591),A_593)
      | ~ r1_tarski(A_593,A_592) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17444,c_1823])).

tff(c_191,plain,(
    ! [A_74] :
      ( k5_relat_1(A_74,k6_relat_1(k2_relat_1(A_74))) = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_200,plain,(
    ! [A_49] :
      ( k5_relat_1(k6_relat_1(A_49),k6_relat_1(A_49)) = k6_relat_1(A_49)
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_191])).

tff(c_204,plain,(
    ! [A_49] : k5_relat_1(k6_relat_1(A_49),k6_relat_1(A_49)) = k6_relat_1(A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_200])).

tff(c_557,plain,(
    ! [A_49] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_49)),k1_relat_1(k6_relat_1(A_49)))
      | ~ v1_relat_1(k6_relat_1(A_49))
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_542])).

tff(c_571,plain,(
    ! [A_49] : r1_tarski(A_49,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_32,c_32,c_557])).

tff(c_684,plain,(
    ! [A_123,B_124] :
      ( k5_relat_1(k6_relat_1(A_123),B_124) = B_124
      | ~ r1_tarski(k1_relat_1(B_124),A_123)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_719,plain,(
    ! [B_125] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_125)),B_125) = B_125
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_571,c_684])).

tff(c_751,plain,(
    ! [B_59] :
      ( k7_relat_1(B_59,k1_relat_1(B_59)) = B_59
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_719])).

tff(c_23280,plain,(
    ! [A_591,A_592] :
      ( k7_relat_1(k6_relat_1(A_591),k1_relat_1(k7_relat_1(k6_relat_1(A_591),A_592))) = k7_relat_1(k6_relat_1(A_591),A_592)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_591),A_592))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_591),A_592))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_591),A_592)),A_592) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23138,c_751])).

tff(c_23430,plain,(
    ! [A_594,A_595] : k7_relat_1(k6_relat_1(A_594),k3_xboole_0(A_594,A_595)) = k7_relat_1(k6_relat_1(A_594),A_595) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_398,c_456,c_456,c_398,c_23280])).

tff(c_864,plain,(
    ! [A_134,A_135] :
      ( k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_135)) = k6_relat_1(A_134)
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_630])).

tff(c_880,plain,(
    ! [A_135,A_134] :
      ( k7_relat_1(k6_relat_1(A_135),A_134) = k6_relat_1(A_134)
      | ~ v1_relat_1(k6_relat_1(A_135))
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_46])).

tff(c_928,plain,(
    ! [A_135,A_134] :
      ( k7_relat_1(k6_relat_1(A_135),A_134) = k6_relat_1(A_134)
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_880])).

tff(c_23584,plain,(
    ! [A_594,A_595] :
      ( k7_relat_1(k6_relat_1(A_594),A_595) = k6_relat_1(k3_xboole_0(A_594,A_595))
      | ~ r1_tarski(k3_xboole_0(A_594,A_595),A_594) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23430,c_928])).

tff(c_23762,plain,(
    ! [A_594,A_595] : k7_relat_1(k6_relat_1(A_594),A_595) = k6_relat_1(k3_xboole_0(A_594,A_595)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_23584])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_323,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_48])).

tff(c_348,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_323])).

tff(c_23826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23762,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.47/4.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.72  
% 11.47/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.72  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 11.47/4.72  
% 11.47/4.72  %Foreground sorts:
% 11.47/4.72  
% 11.47/4.72  
% 11.47/4.72  %Background operators:
% 11.47/4.72  
% 11.47/4.72  
% 11.47/4.72  %Foreground operators:
% 11.47/4.72  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 11.47/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.47/4.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.47/4.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.47/4.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.47/4.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.47/4.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.47/4.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.47/4.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.47/4.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.47/4.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.47/4.72  tff('#skF_2', type, '#skF_2': $i).
% 11.47/4.72  tff('#skF_1', type, '#skF_1': $i).
% 11.47/4.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.47/4.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.47/4.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.47/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.47/4.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.47/4.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.47/4.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.47/4.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.47/4.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.47/4.72  
% 11.47/4.74  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.47/4.74  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.47/4.74  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 11.47/4.74  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.47/4.74  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 11.47/4.74  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 11.47/4.74  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 11.47/4.74  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 11.47/4.74  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 11.47/4.74  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 11.47/4.74  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 11.47/4.74  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 11.47/4.74  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 11.47/4.74  tff(f_109, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 11.47/4.74  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.47/4.74  tff(c_110, plain, (![A_66, B_67]: (k1_setfam_1(k2_tarski(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.47/4.74  tff(c_134, plain, (![B_70, A_71]: (k1_setfam_1(k2_tarski(B_70, A_71))=k3_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_4, c_110])).
% 11.47/4.74  tff(c_18, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.47/4.74  tff(c_140, plain, (![B_70, A_71]: (k3_xboole_0(B_70, A_71)=k3_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_134, c_18])).
% 11.47/4.74  tff(c_22, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.47/4.74  tff(c_32, plain, (![A_49]: (k1_relat_1(k6_relat_1(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.47/4.74  tff(c_371, plain, (![B_93, A_94]: (k3_xboole_0(k1_relat_1(B_93), A_94)=k1_relat_1(k7_relat_1(B_93, A_94)) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.47/4.74  tff(c_394, plain, (![A_49, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_49), A_94))=k3_xboole_0(A_49, A_94) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_371])).
% 11.47/4.74  tff(c_398, plain, (![A_49, A_94]: (k1_relat_1(k7_relat_1(k6_relat_1(A_49), A_94))=k3_xboole_0(A_49, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_394])).
% 11.47/4.74  tff(c_46, plain, (![A_58, B_59]: (k5_relat_1(k6_relat_1(A_58), B_59)=k7_relat_1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.47/4.74  tff(c_542, plain, (![A_108, B_109]: (r1_tarski(k1_relat_1(k5_relat_1(A_108, B_109)), k1_relat_1(A_108)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.47/4.74  tff(c_551, plain, (![B_59, A_58]: (r1_tarski(k1_relat_1(k7_relat_1(B_59, A_58)), k1_relat_1(k6_relat_1(A_58))) | ~v1_relat_1(B_59) | ~v1_relat_1(k6_relat_1(A_58)) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_46, c_542])).
% 11.47/4.74  tff(c_578, plain, (![B_111, A_112]: (r1_tarski(k1_relat_1(k7_relat_1(B_111, A_112)), A_112) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32, c_551])).
% 11.47/4.74  tff(c_584, plain, (![A_49, A_94]: (r1_tarski(k3_xboole_0(A_49, A_94), A_94) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_398, c_578])).
% 11.47/4.74  tff(c_593, plain, (![A_113, A_114]: (r1_tarski(k3_xboole_0(A_113, A_114), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_584])).
% 11.47/4.74  tff(c_602, plain, (![B_70, A_71]: (r1_tarski(k3_xboole_0(B_70, A_71), B_70))), inference(superposition, [status(thm), theory('equality')], [c_140, c_593])).
% 11.47/4.74  tff(c_590, plain, (![A_49, A_94]: (r1_tarski(k3_xboole_0(A_49, A_94), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_584])).
% 11.47/4.74  tff(c_24, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=k8_relat_1(A_37, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.47/4.74  tff(c_302, plain, (![A_88, B_89]: (k5_relat_1(k6_relat_1(A_88), B_89)=k7_relat_1(B_89, A_88) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.47/4.74  tff(c_330, plain, (![A_37, A_88]: (k8_relat_1(A_37, k6_relat_1(A_88))=k7_relat_1(k6_relat_1(A_37), A_88) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_302])).
% 11.47/4.74  tff(c_436, plain, (![A_98, A_99]: (k8_relat_1(A_98, k6_relat_1(A_99))=k7_relat_1(k6_relat_1(A_98), A_99))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_330])).
% 11.47/4.74  tff(c_249, plain, (![B_83, A_84]: (k5_relat_1(B_83, k6_relat_1(A_84))=k8_relat_1(A_84, B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.47/4.74  tff(c_20, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.47/4.74  tff(c_255, plain, (![A_84, B_83]: (v1_relat_1(k8_relat_1(A_84, B_83)) | ~v1_relat_1(k6_relat_1(A_84)) | ~v1_relat_1(B_83) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_249, c_20])).
% 11.47/4.74  tff(c_278, plain, (![A_84, B_83]: (v1_relat_1(k8_relat_1(A_84, B_83)) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_255])).
% 11.47/4.74  tff(c_446, plain, (![A_98, A_99]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_99)) | ~v1_relat_1(k6_relat_1(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_436, c_278])).
% 11.47/4.74  tff(c_456, plain, (![A_98, A_99]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_446])).
% 11.47/4.74  tff(c_351, plain, (![A_37, A_88]: (k8_relat_1(A_37, k6_relat_1(A_88))=k7_relat_1(k6_relat_1(A_37), A_88))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_330])).
% 11.47/4.74  tff(c_1778, plain, (![A_158, B_159, C_160]: (k8_relat_1(A_158, k5_relat_1(B_159, C_160))=k5_relat_1(B_159, k8_relat_1(A_158, C_160)) | ~v1_relat_1(C_160) | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.47/4.74  tff(c_1813, plain, (![B_38, A_158, A_37]: (k5_relat_1(B_38, k8_relat_1(A_158, k6_relat_1(A_37)))=k8_relat_1(A_158, k8_relat_1(A_37, B_38)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1778])).
% 11.47/4.74  tff(c_5450, plain, (![B_238, A_239, A_240]: (k5_relat_1(B_238, k7_relat_1(k6_relat_1(A_239), A_240))=k8_relat_1(A_239, k8_relat_1(A_240, B_238)) | ~v1_relat_1(B_238))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_351, c_1813])).
% 11.47/4.74  tff(c_5475, plain, (![A_239, A_240, A_58]: (k8_relat_1(A_239, k8_relat_1(A_240, k6_relat_1(A_58)))=k7_relat_1(k7_relat_1(k6_relat_1(A_239), A_240), A_58) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_239), A_240)) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_5450, c_46])).
% 11.47/4.74  tff(c_5525, plain, (![A_239, A_240, A_58]: (k8_relat_1(A_239, k7_relat_1(k6_relat_1(A_240), A_58))=k7_relat_1(k7_relat_1(k6_relat_1(A_239), A_240), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_456, c_351, c_5475])).
% 11.47/4.74  tff(c_1810, plain, (![A_58, A_158, B_59]: (k5_relat_1(k6_relat_1(A_58), k8_relat_1(A_158, B_59))=k8_relat_1(A_158, k7_relat_1(B_59, A_58)) | ~v1_relat_1(B_59) | ~v1_relat_1(k6_relat_1(A_58)) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1778])).
% 11.47/4.74  tff(c_4573, plain, (![A_225, A_226, B_227]: (k5_relat_1(k6_relat_1(A_225), k8_relat_1(A_226, B_227))=k8_relat_1(A_226, k7_relat_1(B_227, A_225)) | ~v1_relat_1(B_227))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1810])).
% 11.47/4.74  tff(c_4617, plain, (![A_225, A_37, A_88]: (k5_relat_1(k6_relat_1(A_225), k7_relat_1(k6_relat_1(A_37), A_88))=k8_relat_1(A_37, k7_relat_1(k6_relat_1(A_88), A_225)) | ~v1_relat_1(k6_relat_1(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_4573])).
% 11.47/4.74  tff(c_4634, plain, (![A_225, A_37, A_88]: (k5_relat_1(k6_relat_1(A_225), k7_relat_1(k6_relat_1(A_37), A_88))=k8_relat_1(A_37, k7_relat_1(k6_relat_1(A_88), A_225)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4617])).
% 11.47/4.74  tff(c_17444, plain, (![A_225, A_37, A_88]: (k5_relat_1(k6_relat_1(A_225), k7_relat_1(k6_relat_1(A_37), A_88))=k7_relat_1(k7_relat_1(k6_relat_1(A_37), A_88), A_225))), inference(demodulation, [status(thm), theory('equality')], [c_5525, c_4634])).
% 11.47/4.74  tff(c_34, plain, (![A_49]: (k2_relat_1(k6_relat_1(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.47/4.74  tff(c_623, plain, (![B_117, A_118]: (k5_relat_1(B_117, k6_relat_1(A_118))=B_117 | ~r1_tarski(k2_relat_1(B_117), A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.47/4.74  tff(c_630, plain, (![A_49, A_118]: (k5_relat_1(k6_relat_1(A_49), k6_relat_1(A_118))=k6_relat_1(A_49) | ~r1_tarski(A_49, A_118) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_623])).
% 11.47/4.74  tff(c_633, plain, (![A_49, A_118]: (k5_relat_1(k6_relat_1(A_49), k6_relat_1(A_118))=k6_relat_1(A_49) | ~r1_tarski(A_49, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_630])).
% 11.47/4.74  tff(c_1800, plain, (![A_49, A_158, A_118]: (k5_relat_1(k6_relat_1(A_49), k8_relat_1(A_158, k6_relat_1(A_118)))=k8_relat_1(A_158, k6_relat_1(A_49)) | ~v1_relat_1(k6_relat_1(A_118)) | ~v1_relat_1(k6_relat_1(A_49)) | ~r1_tarski(A_49, A_118))), inference(superposition, [status(thm), theory('equality')], [c_633, c_1778])).
% 11.47/4.74  tff(c_1823, plain, (![A_49, A_158, A_118]: (k5_relat_1(k6_relat_1(A_49), k7_relat_1(k6_relat_1(A_158), A_118))=k7_relat_1(k6_relat_1(A_158), A_49) | ~r1_tarski(A_49, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_351, c_351, c_1800])).
% 11.47/4.74  tff(c_23138, plain, (![A_591, A_592, A_593]: (k7_relat_1(k7_relat_1(k6_relat_1(A_591), A_592), A_593)=k7_relat_1(k6_relat_1(A_591), A_593) | ~r1_tarski(A_593, A_592))), inference(demodulation, [status(thm), theory('equality')], [c_17444, c_1823])).
% 11.47/4.74  tff(c_191, plain, (![A_74]: (k5_relat_1(A_74, k6_relat_1(k2_relat_1(A_74)))=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.47/4.74  tff(c_200, plain, (![A_49]: (k5_relat_1(k6_relat_1(A_49), k6_relat_1(A_49))=k6_relat_1(A_49) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_191])).
% 11.47/4.74  tff(c_204, plain, (![A_49]: (k5_relat_1(k6_relat_1(A_49), k6_relat_1(A_49))=k6_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_200])).
% 11.47/4.74  tff(c_557, plain, (![A_49]: (r1_tarski(k1_relat_1(k6_relat_1(A_49)), k1_relat_1(k6_relat_1(A_49))) | ~v1_relat_1(k6_relat_1(A_49)) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_542])).
% 11.47/4.74  tff(c_571, plain, (![A_49]: (r1_tarski(A_49, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_32, c_32, c_557])).
% 11.47/4.74  tff(c_684, plain, (![A_123, B_124]: (k5_relat_1(k6_relat_1(A_123), B_124)=B_124 | ~r1_tarski(k1_relat_1(B_124), A_123) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.47/4.74  tff(c_719, plain, (![B_125]: (k5_relat_1(k6_relat_1(k1_relat_1(B_125)), B_125)=B_125 | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_571, c_684])).
% 11.47/4.74  tff(c_751, plain, (![B_59]: (k7_relat_1(B_59, k1_relat_1(B_59))=B_59 | ~v1_relat_1(B_59) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_46, c_719])).
% 11.47/4.74  tff(c_23280, plain, (![A_591, A_592]: (k7_relat_1(k6_relat_1(A_591), k1_relat_1(k7_relat_1(k6_relat_1(A_591), A_592)))=k7_relat_1(k6_relat_1(A_591), A_592) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_591), A_592)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_591), A_592)) | ~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_591), A_592)), A_592))), inference(superposition, [status(thm), theory('equality')], [c_23138, c_751])).
% 11.47/4.74  tff(c_23430, plain, (![A_594, A_595]: (k7_relat_1(k6_relat_1(A_594), k3_xboole_0(A_594, A_595))=k7_relat_1(k6_relat_1(A_594), A_595))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_398, c_456, c_456, c_398, c_23280])).
% 11.47/4.74  tff(c_864, plain, (![A_134, A_135]: (k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_135))=k6_relat_1(A_134) | ~r1_tarski(A_134, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_630])).
% 11.47/4.74  tff(c_880, plain, (![A_135, A_134]: (k7_relat_1(k6_relat_1(A_135), A_134)=k6_relat_1(A_134) | ~v1_relat_1(k6_relat_1(A_135)) | ~r1_tarski(A_134, A_135))), inference(superposition, [status(thm), theory('equality')], [c_864, c_46])).
% 11.47/4.74  tff(c_928, plain, (![A_135, A_134]: (k7_relat_1(k6_relat_1(A_135), A_134)=k6_relat_1(A_134) | ~r1_tarski(A_134, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_880])).
% 11.47/4.74  tff(c_23584, plain, (![A_594, A_595]: (k7_relat_1(k6_relat_1(A_594), A_595)=k6_relat_1(k3_xboole_0(A_594, A_595)) | ~r1_tarski(k3_xboole_0(A_594, A_595), A_594))), inference(superposition, [status(thm), theory('equality')], [c_23430, c_928])).
% 11.47/4.74  tff(c_23762, plain, (![A_594, A_595]: (k7_relat_1(k6_relat_1(A_594), A_595)=k6_relat_1(k3_xboole_0(A_594, A_595)))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_23584])).
% 11.47/4.74  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.47/4.74  tff(c_323, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_302, c_48])).
% 11.47/4.74  tff(c_348, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_323])).
% 11.47/4.74  tff(c_23826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23762, c_348])).
% 11.47/4.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/4.74  
% 11.47/4.74  Inference rules
% 11.47/4.74  ----------------------
% 11.47/4.74  #Ref     : 0
% 11.47/4.74  #Sup     : 5867
% 11.47/4.74  #Fact    : 0
% 11.47/4.74  #Define  : 0
% 11.47/4.74  #Split   : 2
% 11.47/4.74  #Chain   : 0
% 11.47/4.74  #Close   : 0
% 11.47/4.74  
% 11.47/4.74  Ordering : KBO
% 11.47/4.74  
% 11.47/4.74  Simplification rules
% 11.47/4.74  ----------------------
% 11.47/4.74  #Subsume      : 830
% 11.47/4.74  #Demod        : 5182
% 11.47/4.74  #Tautology    : 2321
% 11.47/4.74  #SimpNegUnit  : 0
% 11.47/4.74  #BackRed      : 43
% 11.47/4.74  
% 11.47/4.74  #Partial instantiations: 0
% 11.47/4.74  #Strategies tried      : 1
% 11.47/4.74  
% 11.47/4.74  Timing (in seconds)
% 11.47/4.74  ----------------------
% 11.47/4.74  Preprocessing        : 0.37
% 11.47/4.74  Parsing              : 0.21
% 11.47/4.74  CNF conversion       : 0.02
% 11.47/4.74  Main loop            : 3.59
% 11.47/4.74  Inferencing          : 0.71
% 11.47/4.74  Reduction            : 1.71
% 11.47/4.74  Demodulation         : 1.48
% 11.47/4.74  BG Simplification    : 0.09
% 11.47/4.74  Subsumption          : 0.87
% 11.47/4.75  Abstraction          : 0.14
% 11.47/4.75  MUC search           : 0.00
% 11.47/4.75  Cooper               : 0.00
% 11.47/4.75  Total                : 4.00
% 11.47/4.75  Index Insertion      : 0.00
% 11.47/4.75  Index Deletion       : 0.00
% 11.47/4.75  Index Matching       : 0.00
% 11.47/4.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
