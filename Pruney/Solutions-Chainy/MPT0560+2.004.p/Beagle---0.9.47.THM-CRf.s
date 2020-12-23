%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 14.24s
% Output     : CNFRefutation 14.35s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 256 expanded)
%              Number of leaves         :   40 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  179 ( 397 expanded)
%              Number of equality atoms :   56 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_535,plain,(
    ! [B_97,A_98] :
      ( k5_relat_1(B_97,k6_relat_1(A_98)) = k8_relat_1(A_98,B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_542,plain,(
    ! [A_98,A_40] :
      ( k8_relat_1(A_98,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_98),A_40)
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_44])).

tff(c_552,plain,(
    ! [A_98,A_40] : k8_relat_1(A_98,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_98),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_542])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [B_68,A_69] : k1_setfam_1(k2_tarski(B_68,A_69)) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_143])).

tff(c_20,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_20])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k8_relat_1(A_23,B_24),B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_177,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(k8_relat_1(A_23,B_24),B_24) = k8_relat_1(A_23,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_167])).

tff(c_756,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(B_115,k8_relat_1(A_116,B_115)) = k8_relat_1(A_116,B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_177])).

tff(c_339,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k4_xboole_0(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_348,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(k3_xboole_0(A_77,B_78))
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_26])).

tff(c_783,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k8_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_348])).

tff(c_786,plain,(
    ! [A_98,A_40] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_783])).

tff(c_788,plain,(
    ! [A_98,A_40] : v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_786])).

tff(c_556,plain,(
    ! [A_99,A_100] : k8_relat_1(A_99,k6_relat_1(A_100)) = k7_relat_1(k6_relat_1(A_99),A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_542])).

tff(c_562,plain,(
    ! [A_99,A_100] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_99),A_100),k6_relat_1(A_100))
      | ~ v1_relat_1(k6_relat_1(A_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_28])).

tff(c_568,plain,(
    ! [A_99,A_100] : r1_tarski(k7_relat_1(k6_relat_1(A_99),A_100),k6_relat_1(A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_562])).

tff(c_40,plain,(
    ! [A_37] : k2_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ! [A_37] : k1_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_111,plain,(
    ! [A_57] :
      ( k7_relat_1(A_57,k1_relat_1(A_57)) = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_123,plain,(
    ! [A_37] :
      ( k7_relat_1(k6_relat_1(A_37),A_37) = k6_relat_1(A_37)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_111])).

tff(c_127,plain,(
    ! [A_37] : k7_relat_1(k6_relat_1(A_37),A_37) = k6_relat_1(A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_123])).

tff(c_460,plain,(
    ! [B_89,A_90] :
      ( k2_relat_1(k7_relat_1(B_89,A_90)) = k9_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_469,plain,(
    ! [A_37] :
      ( k9_relat_1(k6_relat_1(A_37),A_37) = k2_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_460])).

tff(c_476,plain,(
    ! [A_37] : k9_relat_1(k6_relat_1(A_37),A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_40,c_469])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k5_relat_1(B_26,k6_relat_1(A_25)) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1016,plain,(
    ! [B_132,C_133,A_134] :
      ( k9_relat_1(k5_relat_1(B_132,C_133),A_134) = k9_relat_1(C_133,k9_relat_1(B_132,A_134))
      | ~ v1_relat_1(C_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1039,plain,(
    ! [A_25,B_26,A_134] :
      ( k9_relat_1(k6_relat_1(A_25),k9_relat_1(B_26,A_134)) = k9_relat_1(k8_relat_1(A_25,B_26),A_134)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1016])).

tff(c_2188,plain,(
    ! [A_181,B_182,A_183] :
      ( k9_relat_1(k6_relat_1(A_181),k9_relat_1(B_182,A_183)) = k9_relat_1(k8_relat_1(A_181,B_182),A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1039])).

tff(c_2249,plain,(
    ! [A_181,A_37] :
      ( k9_relat_1(k8_relat_1(A_181,k6_relat_1(A_37)),A_37) = k9_relat_1(k6_relat_1(A_181),A_37)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_2188])).

tff(c_2273,plain,(
    ! [A_181,A_37] : k9_relat_1(k7_relat_1(k6_relat_1(A_181),A_37),A_37) = k9_relat_1(k6_relat_1(A_181),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_552,c_2249])).

tff(c_802,plain,(
    ! [B_121,A_122,C_123] :
      ( r1_tarski(k9_relat_1(B_121,A_122),k9_relat_1(C_123,A_122))
      | ~ r1_tarski(B_121,C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_823,plain,(
    ! [B_121,A_37] :
      ( r1_tarski(k9_relat_1(B_121,A_37),A_37)
      | ~ r1_tarski(B_121,k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_802])).

tff(c_7011,plain,(
    ! [B_314,A_315] :
      ( r1_tarski(k9_relat_1(B_314,A_315),A_315)
      | ~ r1_tarski(B_314,k6_relat_1(A_315))
      | ~ v1_relat_1(B_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_823])).

tff(c_7097,plain,(
    ! [A_181,A_37] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_181),A_37),A_37)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_181),A_37),k6_relat_1(A_37))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_181),A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2273,c_7011])).

tff(c_7159,plain,(
    ! [A_316,A_317] : r1_tarski(k9_relat_1(k6_relat_1(A_316),A_317),A_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_568,c_7097])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13398,plain,(
    ! [A_519,A_520] : k3_xboole_0(k9_relat_1(k6_relat_1(A_519),A_520),A_520) = k9_relat_1(k6_relat_1(A_519),A_520) ),
    inference(resolution,[status(thm)],[c_7159,c_12])).

tff(c_42,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_39,A_38)),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_486,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(A_92,C_93)
      | ~ r1_tarski(B_94,C_93)
      | ~ r1_tarski(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_499,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,'#skF_3')
      | ~ r1_tarski(A_95,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_486])).

tff(c_512,plain,(
    ! [B_39] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_39,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_591,plain,(
    ! [B_103,A_104] :
      ( k7_relat_1(B_103,A_104) = B_103
      | ~ r1_tarski(k1_relat_1(B_103),A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1355,plain,(
    ! [B_154] :
      ( k7_relat_1(k7_relat_1(B_154,'#skF_2'),'#skF_3') = k7_relat_1(B_154,'#skF_2')
      | ~ v1_relat_1(k7_relat_1(B_154,'#skF_2'))
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_512,c_591])).

tff(c_1367,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1('#skF_2'),'#skF_2'),'#skF_3') = k7_relat_1(k6_relat_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1355])).

tff(c_1378,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_127,c_127,c_1367])).

tff(c_1397,plain,(
    r1_tarski(k6_relat_1('#skF_2'),k6_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_568])).

tff(c_820,plain,(
    ! [A_37,C_123] :
      ( r1_tarski(A_37,k9_relat_1(C_123,A_37))
      | ~ r1_tarski(k6_relat_1(A_37),C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_802])).

tff(c_4195,plain,(
    ! [A_240,C_241] :
      ( r1_tarski(A_240,k9_relat_1(C_241,A_240))
      | ~ r1_tarski(k6_relat_1(A_240),C_241)
      | ~ v1_relat_1(C_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_820])).

tff(c_4201,plain,
    ( r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1397,c_4195])).

tff(c_4215,plain,(
    r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4201])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4541,plain,(
    ! [A_249] :
      ( r1_tarski(A_249,k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'))
      | ~ r1_tarski(A_249,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4215,c_10])).

tff(c_5078,plain,(
    ! [A_264] :
      ( k3_xboole_0(A_264,k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = A_264
      | ~ r1_tarski(A_264,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4541,c_12])).

tff(c_5117,plain,(
    ! [A_264] :
      ( k3_xboole_0(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'),A_264) = A_264
      | ~ r1_tarski(A_264,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5078,c_199])).

tff(c_13405,plain,
    ( k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13398,c_5117])).

tff(c_13478,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13405])).

tff(c_1042,plain,(
    ! [B_41,A_40,A_134] :
      ( k9_relat_1(B_41,k9_relat_1(k6_relat_1(A_40),A_134)) = k9_relat_1(k7_relat_1(B_41,A_40),A_134)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1016])).

tff(c_1048,plain,(
    ! [B_41,A_40,A_134] :
      ( k9_relat_1(B_41,k9_relat_1(k6_relat_1(A_40),A_134)) = k9_relat_1(k7_relat_1(B_41,A_40),A_134)
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1042])).

tff(c_32641,plain,(
    ! [B_768] :
      ( k9_relat_1(k7_relat_1(B_768,'#skF_3'),'#skF_2') = k9_relat_1(B_768,'#skF_2')
      | ~ v1_relat_1(B_768) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13478,c_1048])).

tff(c_50,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32773,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32641,c_50])).

tff(c_32828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.24/6.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.24/6.59  
% 14.24/6.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.24/6.59  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 14.24/6.59  
% 14.24/6.59  %Foreground sorts:
% 14.24/6.59  
% 14.24/6.59  
% 14.24/6.59  %Background operators:
% 14.24/6.59  
% 14.24/6.59  
% 14.24/6.59  %Foreground operators:
% 14.24/6.59  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 14.24/6.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.24/6.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.24/6.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.24/6.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.24/6.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.24/6.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.24/6.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.24/6.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.24/6.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.24/6.59  tff('#skF_2', type, '#skF_2': $i).
% 14.24/6.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.24/6.59  tff('#skF_3', type, '#skF_3': $i).
% 14.24/6.59  tff('#skF_1', type, '#skF_1': $i).
% 14.24/6.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.24/6.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.24/6.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.24/6.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.24/6.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.24/6.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.24/6.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.24/6.59  
% 14.35/6.61  tff(f_119, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 14.35/6.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.35/6.61  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.35/6.61  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 14.35/6.61  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 14.35/6.61  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.35/6.61  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.35/6.61  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 14.35/6.61  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.35/6.61  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.35/6.61  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 14.35/6.61  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 14.35/6.61  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 14.35/6.61  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 14.35/6.61  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 14.35/6.61  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 14.35/6.61  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 14.35/6.61  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.35/6.61  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 14.35/6.61  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.35/6.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.35/6.61  tff(c_22, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.35/6.61  tff(c_535, plain, (![B_97, A_98]: (k5_relat_1(B_97, k6_relat_1(A_98))=k8_relat_1(A_98, B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.35/6.61  tff(c_44, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.35/6.61  tff(c_542, plain, (![A_98, A_40]: (k8_relat_1(A_98, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_98), A_40) | ~v1_relat_1(k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_535, c_44])).
% 14.35/6.61  tff(c_552, plain, (![A_98, A_40]: (k8_relat_1(A_98, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_98), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_542])).
% 14.35/6.61  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.35/6.61  tff(c_143, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.35/6.61  tff(c_193, plain, (![B_68, A_69]: (k1_setfam_1(k2_tarski(B_68, A_69))=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_16, c_143])).
% 14.35/6.61  tff(c_20, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.35/6.61  tff(c_199, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_193, c_20])).
% 14.35/6.61  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(k8_relat_1(A_23, B_24), B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.35/6.61  tff(c_167, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.35/6.61  tff(c_177, plain, (![A_23, B_24]: (k3_xboole_0(k8_relat_1(A_23, B_24), B_24)=k8_relat_1(A_23, B_24) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_28, c_167])).
% 14.35/6.61  tff(c_756, plain, (![B_115, A_116]: (k3_xboole_0(B_115, k8_relat_1(A_116, B_115))=k8_relat_1(A_116, B_115) | ~v1_relat_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_177])).
% 14.35/6.61  tff(c_339, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.35/6.61  tff(c_26, plain, (![A_21, B_22]: (v1_relat_1(k4_xboole_0(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.35/6.61  tff(c_348, plain, (![A_77, B_78]: (v1_relat_1(k3_xboole_0(A_77, B_78)) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_339, c_26])).
% 14.35/6.61  tff(c_783, plain, (![A_117, B_118]: (v1_relat_1(k8_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_756, c_348])).
% 14.35/6.61  tff(c_786, plain, (![A_98, A_40]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_552, c_783])).
% 14.35/6.61  tff(c_788, plain, (![A_98, A_40]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_786])).
% 14.35/6.61  tff(c_556, plain, (![A_99, A_100]: (k8_relat_1(A_99, k6_relat_1(A_100))=k7_relat_1(k6_relat_1(A_99), A_100))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_542])).
% 14.35/6.61  tff(c_562, plain, (![A_99, A_100]: (r1_tarski(k7_relat_1(k6_relat_1(A_99), A_100), k6_relat_1(A_100)) | ~v1_relat_1(k6_relat_1(A_100)))), inference(superposition, [status(thm), theory('equality')], [c_556, c_28])).
% 14.35/6.61  tff(c_568, plain, (![A_99, A_100]: (r1_tarski(k7_relat_1(k6_relat_1(A_99), A_100), k6_relat_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_562])).
% 14.35/6.61  tff(c_40, plain, (![A_37]: (k2_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.35/6.61  tff(c_38, plain, (![A_37]: (k1_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.35/6.61  tff(c_111, plain, (![A_57]: (k7_relat_1(A_57, k1_relat_1(A_57))=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 14.35/6.61  tff(c_123, plain, (![A_37]: (k7_relat_1(k6_relat_1(A_37), A_37)=k6_relat_1(A_37) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_111])).
% 14.35/6.61  tff(c_127, plain, (![A_37]: (k7_relat_1(k6_relat_1(A_37), A_37)=k6_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_123])).
% 14.35/6.61  tff(c_460, plain, (![B_89, A_90]: (k2_relat_1(k7_relat_1(B_89, A_90))=k9_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.35/6.61  tff(c_469, plain, (![A_37]: (k9_relat_1(k6_relat_1(A_37), A_37)=k2_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_460])).
% 14.35/6.61  tff(c_476, plain, (![A_37]: (k9_relat_1(k6_relat_1(A_37), A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_40, c_469])).
% 14.35/6.61  tff(c_30, plain, (![B_26, A_25]: (k5_relat_1(B_26, k6_relat_1(A_25))=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.35/6.61  tff(c_1016, plain, (![B_132, C_133, A_134]: (k9_relat_1(k5_relat_1(B_132, C_133), A_134)=k9_relat_1(C_133, k9_relat_1(B_132, A_134)) | ~v1_relat_1(C_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.35/6.61  tff(c_1039, plain, (![A_25, B_26, A_134]: (k9_relat_1(k6_relat_1(A_25), k9_relat_1(B_26, A_134))=k9_relat_1(k8_relat_1(A_25, B_26), A_134) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(B_26) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1016])).
% 14.35/6.61  tff(c_2188, plain, (![A_181, B_182, A_183]: (k9_relat_1(k6_relat_1(A_181), k9_relat_1(B_182, A_183))=k9_relat_1(k8_relat_1(A_181, B_182), A_183) | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1039])).
% 14.35/6.61  tff(c_2249, plain, (![A_181, A_37]: (k9_relat_1(k8_relat_1(A_181, k6_relat_1(A_37)), A_37)=k9_relat_1(k6_relat_1(A_181), A_37) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_2188])).
% 14.35/6.61  tff(c_2273, plain, (![A_181, A_37]: (k9_relat_1(k7_relat_1(k6_relat_1(A_181), A_37), A_37)=k9_relat_1(k6_relat_1(A_181), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_552, c_2249])).
% 14.35/6.61  tff(c_802, plain, (![B_121, A_122, C_123]: (r1_tarski(k9_relat_1(B_121, A_122), k9_relat_1(C_123, A_122)) | ~r1_tarski(B_121, C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.35/6.61  tff(c_823, plain, (![B_121, A_37]: (r1_tarski(k9_relat_1(B_121, A_37), A_37) | ~r1_tarski(B_121, k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_121))), inference(superposition, [status(thm), theory('equality')], [c_476, c_802])).
% 14.35/6.61  tff(c_7011, plain, (![B_314, A_315]: (r1_tarski(k9_relat_1(B_314, A_315), A_315) | ~r1_tarski(B_314, k6_relat_1(A_315)) | ~v1_relat_1(B_314))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_823])).
% 14.35/6.61  tff(c_7097, plain, (![A_181, A_37]: (r1_tarski(k9_relat_1(k6_relat_1(A_181), A_37), A_37) | ~r1_tarski(k7_relat_1(k6_relat_1(A_181), A_37), k6_relat_1(A_37)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_181), A_37)))), inference(superposition, [status(thm), theory('equality')], [c_2273, c_7011])).
% 14.35/6.61  tff(c_7159, plain, (![A_316, A_317]: (r1_tarski(k9_relat_1(k6_relat_1(A_316), A_317), A_317))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_568, c_7097])).
% 14.35/6.61  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.35/6.61  tff(c_13398, plain, (![A_519, A_520]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_519), A_520), A_520)=k9_relat_1(k6_relat_1(A_519), A_520))), inference(resolution, [status(thm)], [c_7159, c_12])).
% 14.35/6.61  tff(c_42, plain, (![B_39, A_38]: (r1_tarski(k1_relat_1(k7_relat_1(B_39, A_38)), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.35/6.61  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.35/6.61  tff(c_486, plain, (![A_92, C_93, B_94]: (r1_tarski(A_92, C_93) | ~r1_tarski(B_94, C_93) | ~r1_tarski(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.35/6.61  tff(c_499, plain, (![A_95]: (r1_tarski(A_95, '#skF_3') | ~r1_tarski(A_95, '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_486])).
% 14.35/6.61  tff(c_512, plain, (![B_39]: (r1_tarski(k1_relat_1(k7_relat_1(B_39, '#skF_2')), '#skF_3') | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_42, c_499])).
% 14.35/6.61  tff(c_591, plain, (![B_103, A_104]: (k7_relat_1(B_103, A_104)=B_103 | ~r1_tarski(k1_relat_1(B_103), A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.35/6.61  tff(c_1355, plain, (![B_154]: (k7_relat_1(k7_relat_1(B_154, '#skF_2'), '#skF_3')=k7_relat_1(B_154, '#skF_2') | ~v1_relat_1(k7_relat_1(B_154, '#skF_2')) | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_512, c_591])).
% 14.35/6.61  tff(c_1367, plain, (k7_relat_1(k7_relat_1(k6_relat_1('#skF_2'), '#skF_2'), '#skF_3')=k7_relat_1(k6_relat_1('#skF_2'), '#skF_2') | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_1355])).
% 14.35/6.61  tff(c_1378, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_127, c_127, c_1367])).
% 14.35/6.61  tff(c_1397, plain, (r1_tarski(k6_relat_1('#skF_2'), k6_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_568])).
% 14.35/6.61  tff(c_820, plain, (![A_37, C_123]: (r1_tarski(A_37, k9_relat_1(C_123, A_37)) | ~r1_tarski(k6_relat_1(A_37), C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_802])).
% 14.35/6.61  tff(c_4195, plain, (![A_240, C_241]: (r1_tarski(A_240, k9_relat_1(C_241, A_240)) | ~r1_tarski(k6_relat_1(A_240), C_241) | ~v1_relat_1(C_241))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_820])).
% 14.35/6.61  tff(c_4201, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1397, c_4195])).
% 14.35/6.61  tff(c_4215, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4201])).
% 14.35/6.61  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.35/6.61  tff(c_4541, plain, (![A_249]: (r1_tarski(A_249, k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')) | ~r1_tarski(A_249, '#skF_2'))), inference(resolution, [status(thm)], [c_4215, c_10])).
% 14.35/6.61  tff(c_5078, plain, (![A_264]: (k3_xboole_0(A_264, k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))=A_264 | ~r1_tarski(A_264, '#skF_2'))), inference(resolution, [status(thm)], [c_4541, c_12])).
% 14.35/6.61  tff(c_5117, plain, (![A_264]: (k3_xboole_0(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'), A_264)=A_264 | ~r1_tarski(A_264, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5078, c_199])).
% 14.35/6.61  tff(c_13405, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13398, c_5117])).
% 14.35/6.61  tff(c_13478, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13405])).
% 14.35/6.61  tff(c_1042, plain, (![B_41, A_40, A_134]: (k9_relat_1(B_41, k9_relat_1(k6_relat_1(A_40), A_134))=k9_relat_1(k7_relat_1(B_41, A_40), A_134) | ~v1_relat_1(B_41) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1016])).
% 14.35/6.61  tff(c_1048, plain, (![B_41, A_40, A_134]: (k9_relat_1(B_41, k9_relat_1(k6_relat_1(A_40), A_134))=k9_relat_1(k7_relat_1(B_41, A_40), A_134) | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1042])).
% 14.35/6.61  tff(c_32641, plain, (![B_768]: (k9_relat_1(k7_relat_1(B_768, '#skF_3'), '#skF_2')=k9_relat_1(B_768, '#skF_2') | ~v1_relat_1(B_768))), inference(superposition, [status(thm), theory('equality')], [c_13478, c_1048])).
% 14.35/6.61  tff(c_50, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.35/6.61  tff(c_32773, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32641, c_50])).
% 14.35/6.61  tff(c_32828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_32773])).
% 14.35/6.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.35/6.61  
% 14.35/6.61  Inference rules
% 14.35/6.61  ----------------------
% 14.35/6.61  #Ref     : 0
% 14.35/6.61  #Sup     : 7541
% 14.35/6.61  #Fact    : 0
% 14.35/6.61  #Define  : 0
% 14.35/6.61  #Split   : 5
% 14.35/6.61  #Chain   : 0
% 14.35/6.61  #Close   : 0
% 14.35/6.61  
% 14.35/6.61  Ordering : KBO
% 14.35/6.61  
% 14.35/6.61  Simplification rules
% 14.35/6.61  ----------------------
% 14.35/6.61  #Subsume      : 1950
% 14.35/6.61  #Demod        : 5506
% 14.35/6.61  #Tautology    : 1663
% 14.35/6.61  #SimpNegUnit  : 71
% 14.35/6.61  #BackRed      : 11
% 14.35/6.61  
% 14.35/6.61  #Partial instantiations: 0
% 14.35/6.61  #Strategies tried      : 1
% 14.35/6.61  
% 14.35/6.61  Timing (in seconds)
% 14.35/6.61  ----------------------
% 14.35/6.61  Preprocessing        : 0.35
% 14.35/6.61  Parsing              : 0.19
% 14.35/6.61  CNF conversion       : 0.02
% 14.35/6.61  Main loop            : 5.44
% 14.35/6.61  Inferencing          : 1.02
% 14.35/6.61  Reduction            : 2.32
% 14.35/6.61  Demodulation         : 1.89
% 14.35/6.61  BG Simplification    : 0.12
% 14.35/6.61  Subsumption          : 1.68
% 14.35/6.61  Abstraction          : 0.18
% 14.35/6.61  MUC search           : 0.00
% 14.35/6.61  Cooper               : 0.00
% 14.35/6.61  Total                : 5.83
% 14.35/6.61  Index Insertion      : 0.00
% 14.35/6.61  Index Deletion       : 0.00
% 14.35/6.61  Index Matching       : 0.00
% 14.35/6.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
