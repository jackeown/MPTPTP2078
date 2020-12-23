%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:34 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 367 expanded)
%              Number of leaves         :   36 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 ( 604 expanded)
%              Number of equality atoms :   59 ( 204 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_94,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_96,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_32,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_229,plain,(
    ! [A_76,B_77] :
      ( k5_relat_1(k6_relat_1(A_76),B_77) = k7_relat_1(B_77,A_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k6_relat_1(k2_relat_1(A_44))) = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_244,plain,(
    ! [A_76] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_76))),A_76) = k6_relat_1(A_76)
      | ~ v1_relat_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_76)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_42])).

tff(c_275,plain,(
    ! [A_76] : k7_relat_1(k6_relat_1(A_76),A_76) = k6_relat_1(A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_34,c_244])).

tff(c_480,plain,(
    ! [C_108,A_109,B_110] :
      ( k7_relat_1(k7_relat_1(C_108,A_109),B_110) = k7_relat_1(C_108,k3_xboole_0(A_109,B_110))
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_501,plain,(
    ! [A_76,B_110] :
      ( k7_relat_1(k6_relat_1(A_76),k3_xboole_0(A_76,B_110)) = k7_relat_1(k6_relat_1(A_76),B_110)
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_480])).

tff(c_808,plain,(
    ! [A_134,B_135] : k7_relat_1(k6_relat_1(A_134),k3_xboole_0(A_134,B_135)) = k7_relat_1(k6_relat_1(A_134),B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_501])).

tff(c_40,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k5_relat_1(B_43,k6_relat_1(A_42)),B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_248,plain,(
    ! [A_42,A_76] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_42),A_76),k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_40])).

tff(c_277,plain,(
    ! [A_42,A_76] : r1_tarski(k7_relat_1(k6_relat_1(A_42),A_76),k6_relat_1(A_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_248])).

tff(c_828,plain,(
    ! [A_134,B_135] : r1_tarski(k7_relat_1(k6_relat_1(A_134),B_135),k6_relat_1(k3_xboole_0(A_134,B_135))) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_277])).

tff(c_16,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(k7_relat_1(C_18,A_16),B_17) = k7_relat_1(C_18,k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [B_24,A_23] :
      ( k5_relat_1(B_24,k6_relat_1(A_23)) = k8_relat_1(A_23,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    ! [A_23,A_76] :
      ( k8_relat_1(A_23,k6_relat_1(A_76)) = k7_relat_1(k6_relat_1(A_23),A_76)
      | ~ v1_relat_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_20])).

tff(c_271,plain,(
    ! [A_23,A_76] : k8_relat_1(A_23,k6_relat_1(A_76)) = k7_relat_1(k6_relat_1(A_23),A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_236])).

tff(c_390,plain,(
    ! [B_94,A_95] :
      ( k3_xboole_0(B_94,k2_zfmisc_1(k1_relat_1(B_94),A_95)) = k8_relat_1(A_95,B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_407,plain,(
    ! [A_96,B_97] :
      ( v1_relat_1(k8_relat_1(A_96,B_97))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_12])).

tff(c_413,plain,(
    ! [A_23,A_76] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_23),A_76))
      | ~ v1_relat_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_407])).

tff(c_418,plain,(
    ! [A_23,A_76] : v1_relat_1(k7_relat_1(k6_relat_1(A_23),A_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_413])).

tff(c_44,plain,(
    ! [A_45,B_46] :
      ( k5_relat_1(k6_relat_1(A_45),B_46) = k7_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_762,plain,(
    ! [B_131,C_132,A_133] :
      ( k7_relat_1(k5_relat_1(B_131,C_132),A_133) = k5_relat_1(k7_relat_1(B_131,A_133),C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_788,plain,(
    ! [A_45,A_133,B_46] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_45),A_133),B_46) = k7_relat_1(k7_relat_1(B_46,A_45),A_133)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_762])).

tff(c_2746,plain,(
    ! [A_204,A_205,B_206] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_204),A_205),B_206) = k7_relat_1(k7_relat_1(B_206,A_204),A_205)
      | ~ v1_relat_1(B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_788])).

tff(c_2779,plain,(
    ! [A_42,A_204,A_205] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_42),A_204),A_205),k7_relat_1(k6_relat_1(A_204),A_205))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_204),A_205))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2746,c_40])).

tff(c_3621,plain,(
    ! [A_223,A_224,A_225] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_223),A_224),A_225),k7_relat_1(k6_relat_1(A_224),A_225)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_418,c_2779])).

tff(c_3719,plain,(
    ! [A_223,A_16,B_17] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_223),k3_xboole_0(A_16,B_17)),k7_relat_1(k6_relat_1(A_16),B_17))
      | ~ v1_relat_1(k6_relat_1(A_223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3621])).

tff(c_8550,plain,(
    ! [A_298,A_299,B_300] : r1_tarski(k7_relat_1(k6_relat_1(A_298),k3_xboole_0(A_299,B_300)),k7_relat_1(k6_relat_1(A_299),B_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3719])).

tff(c_8680,plain,(
    ! [A_301,B_302] : r1_tarski(k6_relat_1(k3_xboole_0(A_301,B_302)),k7_relat_1(k6_relat_1(A_301),B_302)) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_8550])).

tff(c_298,plain,(
    ! [B_79,A_80] :
      ( k7_relat_1(B_79,A_80) = B_79
      | ~ r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_305,plain,(
    ! [A_40,A_80] :
      ( k7_relat_1(k6_relat_1(A_40),A_80) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_80)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_298])).

tff(c_308,plain,(
    ! [A_40,A_80] :
      ( k7_relat_1(k6_relat_1(A_40),A_80) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_305])).

tff(c_36,plain,(
    ! [A_41] : k4_relat_1(k6_relat_1(A_41)) = k6_relat_1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_173,plain,(
    ! [B_71,A_72] :
      ( k5_relat_1(B_71,k6_relat_1(A_72)) = k8_relat_1(A_72,B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,(
    ! [A_72,B_71] :
      ( r1_tarski(k8_relat_1(A_72,B_71),B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_40])).

tff(c_544,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(k1_relat_1(A_116),k1_relat_1(B_117))
      | ~ r1_tarski(A_116,B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_553,plain,(
    ! [A_116,A_40] :
      ( r1_tarski(k1_relat_1(A_116),A_40)
      | ~ r1_tarski(A_116,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_544])).

tff(c_635,plain,(
    ! [A_121,A_122] :
      ( r1_tarski(k1_relat_1(A_121),A_122)
      | ~ r1_tarski(A_121,k6_relat_1(A_122))
      | ~ v1_relat_1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_553])).

tff(c_46,plain,(
    ! [B_48,A_47] :
      ( k7_relat_1(B_48,A_47) = B_48
      | ~ r1_tarski(k1_relat_1(B_48),A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_698,plain,(
    ! [A_129,A_130] :
      ( k7_relat_1(A_129,A_130) = A_129
      | ~ r1_tarski(A_129,k6_relat_1(A_130))
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_635,c_46])).

tff(c_721,plain,(
    ! [A_72,A_130] :
      ( k7_relat_1(k8_relat_1(A_72,k6_relat_1(A_130)),A_130) = k8_relat_1(A_72,k6_relat_1(A_130))
      | ~ v1_relat_1(k8_relat_1(A_72,k6_relat_1(A_130)))
      | ~ v1_relat_1(k6_relat_1(A_130)) ) ),
    inference(resolution,[status(thm)],[c_187,c_698])).

tff(c_749,plain,(
    ! [A_72,A_130] : k7_relat_1(k7_relat_1(k6_relat_1(A_72),A_130),A_130) = k7_relat_1(k6_relat_1(A_72),A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_418,c_271,c_271,c_271,c_721])).

tff(c_791,plain,(
    ! [B_24,A_133,A_23] :
      ( k5_relat_1(k7_relat_1(B_24,A_133),k6_relat_1(A_23)) = k7_relat_1(k8_relat_1(A_23,B_24),A_133)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_762])).

tff(c_2177,plain,(
    ! [B_185,A_186,A_187] :
      ( k5_relat_1(k7_relat_1(B_185,A_186),k6_relat_1(A_187)) = k7_relat_1(k8_relat_1(A_187,B_185),A_186)
      | ~ v1_relat_1(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_791])).

tff(c_2248,plain,(
    ! [A_187,A_76] :
      ( k7_relat_1(k8_relat_1(A_187,k6_relat_1(A_76)),A_76) = k5_relat_1(k6_relat_1(A_76),k6_relat_1(A_187))
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_2177])).

tff(c_2278,plain,(
    ! [A_76,A_187] : k5_relat_1(k6_relat_1(A_76),k6_relat_1(A_187)) = k7_relat_1(k6_relat_1(A_187),A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_749,c_271,c_2248])).

tff(c_659,plain,(
    ! [B_125,A_126] :
      ( k5_relat_1(k4_relat_1(B_125),k4_relat_1(A_126)) = k4_relat_1(k5_relat_1(A_126,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_677,plain,(
    ! [B_125,A_41] :
      ( k5_relat_1(k4_relat_1(B_125),k6_relat_1(A_41)) = k4_relat_1(k5_relat_1(k6_relat_1(A_41),B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_659])).

tff(c_1230,plain,(
    ! [B_150,A_151] :
      ( k5_relat_1(k4_relat_1(B_150),k6_relat_1(A_151)) = k4_relat_1(k5_relat_1(k6_relat_1(A_151),B_150))
      | ~ v1_relat_1(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_677])).

tff(c_1266,plain,(
    ! [A_151,A_41] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_151),k6_relat_1(A_41))) = k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_151))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1230])).

tff(c_1274,plain,(
    ! [A_151,A_41] : k4_relat_1(k5_relat_1(k6_relat_1(A_151),k6_relat_1(A_41))) = k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1266])).

tff(c_4211,plain,(
    ! [A_237,A_238] : k4_relat_1(k7_relat_1(k6_relat_1(A_237),A_238)) = k7_relat_1(k6_relat_1(A_238),A_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2278,c_2278,c_1274])).

tff(c_4273,plain,(
    ! [A_80,A_40] :
      ( k7_relat_1(k6_relat_1(A_80),A_40) = k4_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_4211])).

tff(c_4815,plain,(
    ! [A_246,A_247] :
      ( k7_relat_1(k6_relat_1(A_246),A_247) = k6_relat_1(A_247)
      | ~ r1_tarski(A_247,A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4273])).

tff(c_4940,plain,(
    ! [A_80,A_40] :
      ( k6_relat_1(A_80) = k6_relat_1(A_40)
      | ~ r1_tarski(A_80,A_40)
      | ~ r1_tarski(A_40,A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_4815])).

tff(c_8682,plain,(
    ! [A_301,B_302] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_301),B_302)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_301,B_302)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_301),B_302),k6_relat_1(k3_xboole_0(A_301,B_302))) ) ),
    inference(resolution,[status(thm)],[c_8680,c_4940])).

tff(c_9533,plain,(
    ! [A_325,B_326] : k6_relat_1(k7_relat_1(k6_relat_1(A_325),B_326)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_325,B_326))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_8682])).

tff(c_9787,plain,(
    ! [A_325,B_326] : k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_325,B_326)))) = k7_relat_1(k6_relat_1(A_325),B_326) ),
    inference(superposition,[status(thm),theory(equality)],[c_9533,c_32])).

tff(c_9882,plain,(
    ! [A_325,B_326] : k7_relat_1(k6_relat_1(A_325),B_326) = k6_relat_1(k3_xboole_0(A_325,B_326)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9787])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_251,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_48])).

tff(c_279,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_251])).

tff(c_10304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9882,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.42/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.58  
% 7.42/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.58  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.42/2.58  
% 7.42/2.58  %Foreground sorts:
% 7.42/2.58  
% 7.42/2.58  
% 7.42/2.58  %Background operators:
% 7.42/2.58  
% 7.42/2.58  
% 7.42/2.58  %Foreground operators:
% 7.42/2.58  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.42/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.42/2.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.42/2.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.42/2.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.42/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.42/2.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.42/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.42/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.42/2.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.42/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.42/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.42/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.42/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.42/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.42/2.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.42/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.42/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.42/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.42/2.58  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.42/2.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.42/2.58  
% 7.65/2.60  tff(f_94, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.65/2.60  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.65/2.60  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.65/2.60  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.65/2.60  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 7.65/2.60  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 7.65/2.60  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 7.65/2.60  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 7.65/2.60  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 7.65/2.60  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 7.65/2.60  tff(f_116, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.65/2.60  tff(f_96, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 7.65/2.60  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 7.65/2.60  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 7.65/2.60  tff(f_119, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 7.65/2.60  tff(c_32, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.60  tff(c_10, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.65/2.60  tff(c_34, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.60  tff(c_229, plain, (![A_76, B_77]: (k5_relat_1(k6_relat_1(A_76), B_77)=k7_relat_1(B_77, A_76) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.65/2.60  tff(c_42, plain, (![A_44]: (k5_relat_1(A_44, k6_relat_1(k2_relat_1(A_44)))=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.65/2.60  tff(c_244, plain, (![A_76]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_76))), A_76)=k6_relat_1(A_76) | ~v1_relat_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_76)))))), inference(superposition, [status(thm), theory('equality')], [c_229, c_42])).
% 7.65/2.60  tff(c_275, plain, (![A_76]: (k7_relat_1(k6_relat_1(A_76), A_76)=k6_relat_1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_34, c_244])).
% 7.65/2.60  tff(c_480, plain, (![C_108, A_109, B_110]: (k7_relat_1(k7_relat_1(C_108, A_109), B_110)=k7_relat_1(C_108, k3_xboole_0(A_109, B_110)) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.65/2.60  tff(c_501, plain, (![A_76, B_110]: (k7_relat_1(k6_relat_1(A_76), k3_xboole_0(A_76, B_110))=k7_relat_1(k6_relat_1(A_76), B_110) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_480])).
% 7.65/2.60  tff(c_808, plain, (![A_134, B_135]: (k7_relat_1(k6_relat_1(A_134), k3_xboole_0(A_134, B_135))=k7_relat_1(k6_relat_1(A_134), B_135))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_501])).
% 7.65/2.60  tff(c_40, plain, (![B_43, A_42]: (r1_tarski(k5_relat_1(B_43, k6_relat_1(A_42)), B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.65/2.60  tff(c_248, plain, (![A_42, A_76]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_76), k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_40])).
% 7.65/2.60  tff(c_277, plain, (![A_42, A_76]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_76), k6_relat_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_248])).
% 7.65/2.60  tff(c_828, plain, (![A_134, B_135]: (r1_tarski(k7_relat_1(k6_relat_1(A_134), B_135), k6_relat_1(k3_xboole_0(A_134, B_135))))), inference(superposition, [status(thm), theory('equality')], [c_808, c_277])).
% 7.65/2.60  tff(c_16, plain, (![C_18, A_16, B_17]: (k7_relat_1(k7_relat_1(C_18, A_16), B_17)=k7_relat_1(C_18, k3_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.65/2.60  tff(c_20, plain, (![B_24, A_23]: (k5_relat_1(B_24, k6_relat_1(A_23))=k8_relat_1(A_23, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.60  tff(c_236, plain, (![A_23, A_76]: (k8_relat_1(A_23, k6_relat_1(A_76))=k7_relat_1(k6_relat_1(A_23), A_76) | ~v1_relat_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_20])).
% 7.65/2.60  tff(c_271, plain, (![A_23, A_76]: (k8_relat_1(A_23, k6_relat_1(A_76))=k7_relat_1(k6_relat_1(A_23), A_76))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_236])).
% 7.65/2.60  tff(c_390, plain, (![B_94, A_95]: (k3_xboole_0(B_94, k2_zfmisc_1(k1_relat_1(B_94), A_95))=k8_relat_1(A_95, B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.65/2.60  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.65/2.60  tff(c_407, plain, (![A_96, B_97]: (v1_relat_1(k8_relat_1(A_96, B_97)) | ~v1_relat_1(B_97) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_390, c_12])).
% 7.65/2.60  tff(c_413, plain, (![A_23, A_76]: (v1_relat_1(k7_relat_1(k6_relat_1(A_23), A_76)) | ~v1_relat_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_271, c_407])).
% 7.65/2.60  tff(c_418, plain, (![A_23, A_76]: (v1_relat_1(k7_relat_1(k6_relat_1(A_23), A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_413])).
% 7.65/2.60  tff(c_44, plain, (![A_45, B_46]: (k5_relat_1(k6_relat_1(A_45), B_46)=k7_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.65/2.60  tff(c_762, plain, (![B_131, C_132, A_133]: (k7_relat_1(k5_relat_1(B_131, C_132), A_133)=k5_relat_1(k7_relat_1(B_131, A_133), C_132) | ~v1_relat_1(C_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.65/2.60  tff(c_788, plain, (![A_45, A_133, B_46]: (k5_relat_1(k7_relat_1(k6_relat_1(A_45), A_133), B_46)=k7_relat_1(k7_relat_1(B_46, A_45), A_133) | ~v1_relat_1(B_46) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_44, c_762])).
% 7.65/2.60  tff(c_2746, plain, (![A_204, A_205, B_206]: (k5_relat_1(k7_relat_1(k6_relat_1(A_204), A_205), B_206)=k7_relat_1(k7_relat_1(B_206, A_204), A_205) | ~v1_relat_1(B_206))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_788])).
% 7.65/2.60  tff(c_2779, plain, (![A_42, A_204, A_205]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_42), A_204), A_205), k7_relat_1(k6_relat_1(A_204), A_205)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_204), A_205)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_2746, c_40])).
% 7.65/2.60  tff(c_3621, plain, (![A_223, A_224, A_225]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_223), A_224), A_225), k7_relat_1(k6_relat_1(A_224), A_225)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_418, c_2779])).
% 7.65/2.60  tff(c_3719, plain, (![A_223, A_16, B_17]: (r1_tarski(k7_relat_1(k6_relat_1(A_223), k3_xboole_0(A_16, B_17)), k7_relat_1(k6_relat_1(A_16), B_17)) | ~v1_relat_1(k6_relat_1(A_223)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3621])).
% 7.65/2.60  tff(c_8550, plain, (![A_298, A_299, B_300]: (r1_tarski(k7_relat_1(k6_relat_1(A_298), k3_xboole_0(A_299, B_300)), k7_relat_1(k6_relat_1(A_299), B_300)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3719])).
% 7.65/2.60  tff(c_8680, plain, (![A_301, B_302]: (r1_tarski(k6_relat_1(k3_xboole_0(A_301, B_302)), k7_relat_1(k6_relat_1(A_301), B_302)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_8550])).
% 7.65/2.60  tff(c_298, plain, (![B_79, A_80]: (k7_relat_1(B_79, A_80)=B_79 | ~r1_tarski(k1_relat_1(B_79), A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.65/2.60  tff(c_305, plain, (![A_40, A_80]: (k7_relat_1(k6_relat_1(A_40), A_80)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_80) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_298])).
% 7.65/2.60  tff(c_308, plain, (![A_40, A_80]: (k7_relat_1(k6_relat_1(A_40), A_80)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_305])).
% 7.65/2.60  tff(c_36, plain, (![A_41]: (k4_relat_1(k6_relat_1(A_41))=k6_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.65/2.60  tff(c_173, plain, (![B_71, A_72]: (k5_relat_1(B_71, k6_relat_1(A_72))=k8_relat_1(A_72, B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.60  tff(c_187, plain, (![A_72, B_71]: (r1_tarski(k8_relat_1(A_72, B_71), B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_173, c_40])).
% 7.65/2.60  tff(c_544, plain, (![A_116, B_117]: (r1_tarski(k1_relat_1(A_116), k1_relat_1(B_117)) | ~r1_tarski(A_116, B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.65/2.60  tff(c_553, plain, (![A_116, A_40]: (r1_tarski(k1_relat_1(A_116), A_40) | ~r1_tarski(A_116, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_32, c_544])).
% 7.65/2.60  tff(c_635, plain, (![A_121, A_122]: (r1_tarski(k1_relat_1(A_121), A_122) | ~r1_tarski(A_121, k6_relat_1(A_122)) | ~v1_relat_1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_553])).
% 7.65/2.60  tff(c_46, plain, (![B_48, A_47]: (k7_relat_1(B_48, A_47)=B_48 | ~r1_tarski(k1_relat_1(B_48), A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.65/2.60  tff(c_698, plain, (![A_129, A_130]: (k7_relat_1(A_129, A_130)=A_129 | ~r1_tarski(A_129, k6_relat_1(A_130)) | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_635, c_46])).
% 7.65/2.60  tff(c_721, plain, (![A_72, A_130]: (k7_relat_1(k8_relat_1(A_72, k6_relat_1(A_130)), A_130)=k8_relat_1(A_72, k6_relat_1(A_130)) | ~v1_relat_1(k8_relat_1(A_72, k6_relat_1(A_130))) | ~v1_relat_1(k6_relat_1(A_130)))), inference(resolution, [status(thm)], [c_187, c_698])).
% 7.65/2.60  tff(c_749, plain, (![A_72, A_130]: (k7_relat_1(k7_relat_1(k6_relat_1(A_72), A_130), A_130)=k7_relat_1(k6_relat_1(A_72), A_130))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_418, c_271, c_271, c_271, c_721])).
% 7.65/2.60  tff(c_791, plain, (![B_24, A_133, A_23]: (k5_relat_1(k7_relat_1(B_24, A_133), k6_relat_1(A_23))=k7_relat_1(k8_relat_1(A_23, B_24), A_133) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(B_24) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_20, c_762])).
% 7.65/2.60  tff(c_2177, plain, (![B_185, A_186, A_187]: (k5_relat_1(k7_relat_1(B_185, A_186), k6_relat_1(A_187))=k7_relat_1(k8_relat_1(A_187, B_185), A_186) | ~v1_relat_1(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_791])).
% 7.65/2.60  tff(c_2248, plain, (![A_187, A_76]: (k7_relat_1(k8_relat_1(A_187, k6_relat_1(A_76)), A_76)=k5_relat_1(k6_relat_1(A_76), k6_relat_1(A_187)) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_275, c_2177])).
% 7.65/2.60  tff(c_2278, plain, (![A_76, A_187]: (k5_relat_1(k6_relat_1(A_76), k6_relat_1(A_187))=k7_relat_1(k6_relat_1(A_187), A_76))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_749, c_271, c_2248])).
% 7.65/2.60  tff(c_659, plain, (![B_125, A_126]: (k5_relat_1(k4_relat_1(B_125), k4_relat_1(A_126))=k4_relat_1(k5_relat_1(A_126, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.65/2.60  tff(c_677, plain, (![B_125, A_41]: (k5_relat_1(k4_relat_1(B_125), k6_relat_1(A_41))=k4_relat_1(k5_relat_1(k6_relat_1(A_41), B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_659])).
% 7.65/2.60  tff(c_1230, plain, (![B_150, A_151]: (k5_relat_1(k4_relat_1(B_150), k6_relat_1(A_151))=k4_relat_1(k5_relat_1(k6_relat_1(A_151), B_150)) | ~v1_relat_1(B_150))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_677])).
% 7.65/2.60  tff(c_1266, plain, (![A_151, A_41]: (k4_relat_1(k5_relat_1(k6_relat_1(A_151), k6_relat_1(A_41)))=k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_151)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1230])).
% 7.65/2.60  tff(c_1274, plain, (![A_151, A_41]: (k4_relat_1(k5_relat_1(k6_relat_1(A_151), k6_relat_1(A_41)))=k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_151)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1266])).
% 7.65/2.60  tff(c_4211, plain, (![A_237, A_238]: (k4_relat_1(k7_relat_1(k6_relat_1(A_237), A_238))=k7_relat_1(k6_relat_1(A_238), A_237))), inference(demodulation, [status(thm), theory('equality')], [c_2278, c_2278, c_1274])).
% 7.65/2.60  tff(c_4273, plain, (![A_80, A_40]: (k7_relat_1(k6_relat_1(A_80), A_40)=k4_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, A_80))), inference(superposition, [status(thm), theory('equality')], [c_308, c_4211])).
% 7.65/2.60  tff(c_4815, plain, (![A_246, A_247]: (k7_relat_1(k6_relat_1(A_246), A_247)=k6_relat_1(A_247) | ~r1_tarski(A_247, A_246))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4273])).
% 7.65/2.60  tff(c_4940, plain, (![A_80, A_40]: (k6_relat_1(A_80)=k6_relat_1(A_40) | ~r1_tarski(A_80, A_40) | ~r1_tarski(A_40, A_80))), inference(superposition, [status(thm), theory('equality')], [c_308, c_4815])).
% 7.65/2.60  tff(c_8682, plain, (![A_301, B_302]: (k6_relat_1(k7_relat_1(k6_relat_1(A_301), B_302))=k6_relat_1(k6_relat_1(k3_xboole_0(A_301, B_302))) | ~r1_tarski(k7_relat_1(k6_relat_1(A_301), B_302), k6_relat_1(k3_xboole_0(A_301, B_302))))), inference(resolution, [status(thm)], [c_8680, c_4940])).
% 7.65/2.60  tff(c_9533, plain, (![A_325, B_326]: (k6_relat_1(k7_relat_1(k6_relat_1(A_325), B_326))=k6_relat_1(k6_relat_1(k3_xboole_0(A_325, B_326))))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_8682])).
% 7.65/2.60  tff(c_9787, plain, (![A_325, B_326]: (k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_325, B_326))))=k7_relat_1(k6_relat_1(A_325), B_326))), inference(superposition, [status(thm), theory('equality')], [c_9533, c_32])).
% 7.65/2.60  tff(c_9882, plain, (![A_325, B_326]: (k7_relat_1(k6_relat_1(A_325), B_326)=k6_relat_1(k3_xboole_0(A_325, B_326)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9787])).
% 7.65/2.60  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.65/2.60  tff(c_251, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_48])).
% 7.65/2.60  tff(c_279, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_251])).
% 7.65/2.60  tff(c_10304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9882, c_279])).
% 7.65/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.60  
% 7.65/2.60  Inference rules
% 7.65/2.60  ----------------------
% 7.65/2.60  #Ref     : 0
% 7.65/2.60  #Sup     : 2338
% 7.65/2.60  #Fact    : 0
% 7.65/2.60  #Define  : 0
% 7.65/2.60  #Split   : 2
% 7.65/2.60  #Chain   : 0
% 7.65/2.60  #Close   : 0
% 7.65/2.60  
% 7.65/2.60  Ordering : KBO
% 7.65/2.60  
% 7.65/2.60  Simplification rules
% 7.65/2.60  ----------------------
% 7.65/2.60  #Subsume      : 224
% 7.65/2.60  #Demod        : 2844
% 7.65/2.60  #Tautology    : 821
% 7.65/2.60  #SimpNegUnit  : 0
% 7.65/2.60  #BackRed      : 74
% 7.65/2.60  
% 7.65/2.60  #Partial instantiations: 0
% 7.65/2.60  #Strategies tried      : 1
% 7.65/2.60  
% 7.65/2.60  Timing (in seconds)
% 7.65/2.60  ----------------------
% 7.65/2.61  Preprocessing        : 0.32
% 7.65/2.61  Parsing              : 0.17
% 7.65/2.61  CNF conversion       : 0.02
% 7.65/2.61  Main loop            : 1.49
% 7.65/2.61  Inferencing          : 0.45
% 7.65/2.61  Reduction            : 0.63
% 7.65/2.61  Demodulation         : 0.50
% 7.65/2.61  BG Simplification    : 0.07
% 7.65/2.61  Subsumption          : 0.25
% 7.65/2.61  Abstraction          : 0.09
% 7.65/2.61  MUC search           : 0.00
% 7.65/2.61  Cooper               : 0.00
% 7.65/2.61  Total                : 1.84
% 7.65/2.61  Index Insertion      : 0.00
% 7.65/2.61  Index Deletion       : 0.00
% 7.65/2.61  Index Matching       : 0.00
% 7.65/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
