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

% Result     : Theorem 35.71s
% Output     : CNFRefutation 35.71s
% Verified   : 
% Statistics : Number of formulae       :  184 (1847 expanded)
%              Number of leaves         :   42 ( 694 expanded)
%              Depth                    :   26
%              Number of atoms          :  319 (3138 expanded)
%              Number of equality atoms :  120 (1172 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [B_82,A_83] : k1_setfam_1(k2_tarski(B_82,A_83)) = k3_xboole_0(A_83,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_20,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [B_84,A_85] : k3_xboole_0(B_84,A_85) = k3_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_20])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_170,plain,(
    ! [B_84,A_85] : r1_tarski(k3_xboole_0(B_84,A_85),A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2])).

tff(c_138,plain,(
    ! [B_82,A_83] : k3_xboole_0(B_82,A_83) = k3_xboole_0(A_83,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_20])).

tff(c_24,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [B_50,A_49] :
      ( k2_relat_1(k7_relat_1(B_50,A_49)) = k9_relat_1(B_50,A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_325,plain,(
    ! [A_104,B_105] :
      ( k5_relat_1(k6_relat_1(A_104),B_105) = k7_relat_1(B_105,A_104)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [B_44,A_43] :
      ( k5_relat_1(B_44,k6_relat_1(A_43)) = k8_relat_1(A_43,B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_332,plain,(
    ! [A_43,A_104] :
      ( k8_relat_1(A_43,k6_relat_1(A_104)) = k7_relat_1(k6_relat_1(A_43),A_104)
      | ~ v1_relat_1(k6_relat_1(A_104))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_28])).

tff(c_370,plain,(
    ! [A_43,A_104] : k8_relat_1(A_43,k6_relat_1(A_104)) = k7_relat_1(k6_relat_1(A_43),A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_332])).

tff(c_40,plain,(
    ! [A_61] : k2_relat_1(k6_relat_1(A_61)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_638,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_144,B_145)),k2_relat_1(B_145))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_647,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_43,B_44)),k2_relat_1(k6_relat_1(A_43)))
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_638])).

tff(c_667,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_146,B_147)),A_146)
      | ~ v1_relat_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40,c_647])).

tff(c_670,plain,(
    ! [A_43,A_104] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_43),A_104)),A_43)
      | ~ v1_relat_1(k6_relat_1(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_667])).

tff(c_678,plain,(
    ! [A_148,A_149] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_148),A_149)),A_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_670])).

tff(c_682,plain,(
    ! [A_148,A_49] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_148),A_49),A_148)
      | ~ v1_relat_1(k6_relat_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_678])).

tff(c_687,plain,(
    ! [A_148,A_49] : r1_tarski(k9_relat_1(k6_relat_1(A_148),A_49),A_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_682])).

tff(c_38,plain,(
    ! [A_61] : k1_relat_1(k6_relat_1(A_61)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_694,plain,(
    ! [A_152,B_153] :
      ( k5_relat_1(k6_relat_1(A_152),B_153) = B_153
      | ~ r1_tarski(k1_relat_1(B_153),A_152)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_710,plain,(
    ! [A_152,A_61] :
      ( k5_relat_1(k6_relat_1(A_152),k6_relat_1(A_61)) = k6_relat_1(A_61)
      | ~ r1_tarski(A_61,A_152)
      | ~ v1_relat_1(k6_relat_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_694])).

tff(c_1106,plain,(
    ! [A_174,A_175] :
      ( k5_relat_1(k6_relat_1(A_174),k6_relat_1(A_175)) = k6_relat_1(A_175)
      | ~ r1_tarski(A_175,A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_710])).

tff(c_1163,plain,(
    ! [A_43,A_174] :
      ( k8_relat_1(A_43,k6_relat_1(A_174)) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_174)
      | ~ v1_relat_1(k6_relat_1(A_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1106])).

tff(c_1279,plain,(
    ! [A_181,A_182] :
      ( k7_relat_1(k6_relat_1(A_181),A_182) = k6_relat_1(A_181)
      | ~ r1_tarski(A_181,A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_370,c_1163])).

tff(c_501,plain,(
    ! [B_126,A_127] :
      ( k3_xboole_0(k1_relat_1(B_126),A_127) = k1_relat_1(k7_relat_1(B_126,A_127))
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_530,plain,(
    ! [A_61,A_127] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_61),A_127)) = k3_xboole_0(A_61,A_127)
      | ~ v1_relat_1(k6_relat_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_501])).

tff(c_534,plain,(
    ! [A_61,A_127] : k1_relat_1(k7_relat_1(k6_relat_1(A_61),A_127)) = k3_xboole_0(A_61,A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_530])).

tff(c_1308,plain,(
    ! [A_181,A_182] :
      ( k3_xboole_0(A_181,A_182) = k1_relat_1(k6_relat_1(A_181))
      | ~ r1_tarski(A_181,A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_534])).

tff(c_1372,plain,(
    ! [A_183,A_184] :
      ( k3_xboole_0(A_183,A_184) = A_183
      | ~ r1_tarski(A_183,A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1308])).

tff(c_3305,plain,(
    ! [A_243,A_244] : k3_xboole_0(k9_relat_1(k6_relat_1(A_243),A_244),A_243) = k9_relat_1(k6_relat_1(A_243),A_244) ),
    inference(resolution,[status(thm)],[c_687,c_1372])).

tff(c_3381,plain,(
    ! [A_83,A_244] : k3_xboole_0(A_83,k9_relat_1(k6_relat_1(A_83),A_244)) = k9_relat_1(k6_relat_1(A_83),A_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_3305])).

tff(c_442,plain,(
    ! [A_117,A_118] : k8_relat_1(A_117,k6_relat_1(A_118)) = k7_relat_1(k6_relat_1(A_117),A_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_332])).

tff(c_278,plain,(
    ! [B_100,A_101] :
      ( k5_relat_1(B_100,k6_relat_1(A_101)) = k8_relat_1(A_101,B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k5_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_287,plain,(
    ! [A_101,B_100] :
      ( v1_relat_1(k8_relat_1(A_101,B_100))
      | ~ v1_relat_1(k6_relat_1(A_101))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_22])).

tff(c_314,plain,(
    ! [A_101,B_100] :
      ( v1_relat_1(k8_relat_1(A_101,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_287])).

tff(c_452,plain,(
    ! [A_117,A_118] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_117),A_118))
      | ~ v1_relat_1(k6_relat_1(A_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_314])).

tff(c_462,plain,(
    ! [A_117,A_118] : v1_relat_1(k7_relat_1(k6_relat_1(A_117),A_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_452])).

tff(c_475,plain,(
    ! [B_123,A_124] :
      ( k2_relat_1(k7_relat_1(B_123,A_124)) = k9_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k6_relat_1(k2_relat_1(A_66))) = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8050,plain,(
    ! [B_329,A_330] :
      ( k5_relat_1(k7_relat_1(B_329,A_330),k6_relat_1(k9_relat_1(B_329,A_330))) = k7_relat_1(B_329,A_330)
      | ~ v1_relat_1(k7_relat_1(B_329,A_330))
      | ~ v1_relat_1(B_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_48])).

tff(c_52,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = k7_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1209,plain,(
    ! [B_176,C_177,A_178] :
      ( k7_relat_1(k5_relat_1(B_176,C_177),A_178) = k5_relat_1(k7_relat_1(B_176,A_178),C_177)
      | ~ v1_relat_1(C_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1254,plain,(
    ! [A_69,A_178,B_70] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_69),A_178),B_70) = k7_relat_1(k7_relat_1(B_70,A_69),A_178)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1209])).

tff(c_1271,plain,(
    ! [A_69,A_178,B_70] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_69),A_178),B_70) = k7_relat_1(k7_relat_1(B_70,A_69),A_178)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1254])).

tff(c_8063,plain,(
    ! [A_69,A_330] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_69),A_330)),A_69),A_330) = k7_relat_1(k6_relat_1(A_69),A_330)
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_69),A_330)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_69),A_330))
      | ~ v1_relat_1(k6_relat_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8050,c_1271])).

tff(c_33550,plain,(
    ! [A_604,A_605] : k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_604),A_605)),A_604),A_605) = k7_relat_1(k6_relat_1(A_604),A_605) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_462,c_24,c_8063])).

tff(c_535,plain,(
    ! [A_128,A_129] : k1_relat_1(k7_relat_1(k6_relat_1(A_128),A_129)) = k3_xboole_0(A_128,A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_530])).

tff(c_50,plain,(
    ! [B_68,A_67] :
      ( k3_xboole_0(k1_relat_1(B_68),A_67) = k1_relat_1(k7_relat_1(B_68,A_67))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_541,plain,(
    ! [A_128,A_129,A_67] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_128),A_129),A_67)) = k3_xboole_0(k3_xboole_0(A_128,A_129),A_67)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_128),A_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_50])).

tff(c_550,plain,(
    ! [A_128,A_129,A_67] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_128),A_129),A_67)) = k3_xboole_0(k3_xboole_0(A_128,A_129),A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_541])).

tff(c_33576,plain,(
    ! [A_604,A_605] : k3_xboole_0(k3_xboole_0(k9_relat_1(k6_relat_1(A_604),A_605),A_604),A_605) = k1_relat_1(k7_relat_1(k6_relat_1(A_604),A_605)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33550,c_550])).

tff(c_33731,plain,(
    ! [A_605,A_604] : k3_xboole_0(A_605,k9_relat_1(k6_relat_1(A_604),A_605)) = k3_xboole_0(A_604,A_605) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3381,c_534,c_138,c_138,c_33576])).

tff(c_205,plain,(
    ! [A_88] :
      ( k5_relat_1(A_88,k6_relat_1(k2_relat_1(A_88))) = A_88
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_214,plain,(
    ! [A_61] :
      ( k5_relat_1(k6_relat_1(A_61),k6_relat_1(A_61)) = k6_relat_1(A_61)
      | ~ v1_relat_1(k6_relat_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_205])).

tff(c_218,plain,(
    ! [A_61] : k5_relat_1(k6_relat_1(A_61),k6_relat_1(A_61)) = k6_relat_1(A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_214])).

tff(c_1263,plain,(
    ! [A_66,A_178] :
      ( k5_relat_1(k7_relat_1(A_66,A_178),k6_relat_1(k2_relat_1(A_66))) = k7_relat_1(A_66,A_178)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_66)))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1209])).

tff(c_2835,plain,(
    ! [A_228,A_229] :
      ( k5_relat_1(k7_relat_1(A_228,A_229),k6_relat_1(k2_relat_1(A_228))) = k7_relat_1(A_228,A_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1263])).

tff(c_2886,plain,(
    ! [A_61,A_229] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_61),A_229),k6_relat_1(A_61)) = k7_relat_1(k6_relat_1(A_61),A_229)
      | ~ v1_relat_1(k6_relat_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2835])).

tff(c_13640,plain,(
    ! [A_385,A_386] : k5_relat_1(k7_relat_1(k6_relat_1(A_385),A_386),k6_relat_1(A_385)) = k7_relat_1(k6_relat_1(A_385),A_386) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2886])).

tff(c_1235,plain,(
    ! [B_176,A_178,C_177] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_176,A_178),C_177)) = k9_relat_1(k5_relat_1(B_176,C_177),A_178)
      | ~ v1_relat_1(k5_relat_1(B_176,C_177))
      | ~ v1_relat_1(C_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_32])).

tff(c_13652,plain,(
    ! [A_385,A_386] :
      ( k9_relat_1(k5_relat_1(k6_relat_1(A_385),k6_relat_1(A_385)),A_386) = k2_relat_1(k7_relat_1(k6_relat_1(A_385),A_386))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_385),k6_relat_1(A_385)))
      | ~ v1_relat_1(k6_relat_1(A_385))
      | ~ v1_relat_1(k6_relat_1(A_385)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13640,c_1235])).

tff(c_13760,plain,(
    ! [A_385,A_386] : k2_relat_1(k7_relat_1(k6_relat_1(A_385),A_386)) = k9_relat_1(k6_relat_1(A_385),A_386) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_24,c_218,c_218,c_13652])).

tff(c_1002,plain,(
    ! [A_167,B_168,C_169] :
      ( k8_relat_1(A_167,k5_relat_1(B_168,C_169)) = k5_relat_1(B_168,k8_relat_1(A_167,C_169))
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1040,plain,(
    ! [A_66,A_167] :
      ( k5_relat_1(A_66,k8_relat_1(A_167,k6_relat_1(k2_relat_1(A_66)))) = k8_relat_1(A_167,A_66)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_66)))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1002])).

tff(c_2615,plain,(
    ! [A_224,A_225] :
      ( k5_relat_1(A_224,k7_relat_1(k6_relat_1(A_225),k2_relat_1(A_224))) = k8_relat_1(A_225,A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_370,c_1040])).

tff(c_2667,plain,(
    ! [A_225,A_69] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_225),k2_relat_1(k6_relat_1(A_69))),A_69) = k8_relat_1(A_225,k6_relat_1(A_69))
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_225),k2_relat_1(k6_relat_1(A_69)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2615])).

tff(c_2692,plain,(
    ! [A_225,A_69] : k7_relat_1(k7_relat_1(k6_relat_1(A_225),A_69),A_69) = k7_relat_1(k6_relat_1(A_225),A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_40,c_24,c_370,c_40,c_2667])).

tff(c_350,plain,(
    ! [A_104] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_104))),A_104) = k6_relat_1(A_104)
      | ~ v1_relat_1(k6_relat_1(A_104))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_104)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_48])).

tff(c_378,plain,(
    ! [A_104] : k7_relat_1(k6_relat_1(A_104),A_104) = k6_relat_1(A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_40,c_350])).

tff(c_1257,plain,(
    ! [B_44,A_178,A_43] :
      ( k5_relat_1(k7_relat_1(B_44,A_178),k6_relat_1(A_43)) = k7_relat_1(k8_relat_1(A_43,B_44),A_178)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1209])).

tff(c_4864,plain,(
    ! [B_291,A_292,A_293] :
      ( k5_relat_1(k7_relat_1(B_291,A_292),k6_relat_1(A_293)) = k7_relat_1(k8_relat_1(A_293,B_291),A_292)
      | ~ v1_relat_1(B_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1257])).

tff(c_4928,plain,(
    ! [A_293,A_104] :
      ( k7_relat_1(k8_relat_1(A_293,k6_relat_1(A_104)),A_104) = k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_293))
      | ~ v1_relat_1(k6_relat_1(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_4864])).

tff(c_4958,plain,(
    ! [A_104,A_293] : k5_relat_1(k6_relat_1(A_104),k6_relat_1(A_293)) = k7_relat_1(k6_relat_1(A_293),A_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2692,c_370,c_4928])).

tff(c_516,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_126,A_127)),k1_relat_1(B_126))
      | ~ v1_relat_1(B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_2])).

tff(c_711,plain,(
    ! [B_126,A_127] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_126)),k7_relat_1(B_126,A_127)) = k7_relat_1(B_126,A_127)
      | ~ v1_relat_1(k7_relat_1(B_126,A_127))
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_516,c_694])).

tff(c_2192,plain,(
    ! [A_208,B_209,C_210] :
      ( k5_relat_1(k5_relat_1(A_208,B_209),C_210) = k5_relat_1(A_208,k5_relat_1(B_209,C_210))
      | ~ v1_relat_1(C_210)
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    ! [B_63,A_62] :
      ( r1_tarski(k5_relat_1(B_63,k6_relat_1(A_62)),B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2219,plain,(
    ! [A_208,B_209,A_62] :
      ( r1_tarski(k5_relat_1(A_208,k5_relat_1(B_209,k6_relat_1(A_62))),k5_relat_1(A_208,B_209))
      | ~ v1_relat_1(k5_relat_1(A_208,B_209))
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2192,c_44])).

tff(c_8718,plain,(
    ! [A_335,B_336,A_337] :
      ( r1_tarski(k5_relat_1(A_335,k5_relat_1(B_336,k6_relat_1(A_337))),k5_relat_1(A_335,B_336))
      | ~ v1_relat_1(k5_relat_1(A_335,B_336))
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2219])).

tff(c_8838,plain,(
    ! [B_44,A_43,A_337] :
      ( r1_tarski(k5_relat_1(B_44,k5_relat_1(k6_relat_1(A_43),k6_relat_1(A_337))),k8_relat_1(A_43,B_44))
      | ~ v1_relat_1(k5_relat_1(B_44,k6_relat_1(A_43)))
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8718])).

tff(c_92188,plain,(
    ! [B_1155,A_1156,A_1157] :
      ( r1_tarski(k5_relat_1(B_1155,k7_relat_1(k6_relat_1(A_1156),A_1157)),k8_relat_1(A_1157,B_1155))
      | ~ v1_relat_1(k5_relat_1(B_1155,k6_relat_1(A_1157)))
      | ~ v1_relat_1(B_1155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4958,c_8838])).

tff(c_92228,plain,(
    ! [A_1156,A_127] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_1156),A_127),k8_relat_1(A_127,k6_relat_1(k1_relat_1(k6_relat_1(A_1156)))))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_1156))),k6_relat_1(A_127)))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_1156))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_1156),A_127))
      | ~ v1_relat_1(k6_relat_1(A_1156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_92188])).

tff(c_92358,plain,(
    ! [A_1156,A_127] : r1_tarski(k7_relat_1(k6_relat_1(A_1156),A_127),k7_relat_1(k6_relat_1(A_127),A_1156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_462,c_24,c_462,c_4958,c_38,c_370,c_38,c_92228])).

tff(c_1311,plain,(
    ! [A_181,A_182] :
      ( k9_relat_1(k6_relat_1(A_181),A_182) = k2_relat_1(k6_relat_1(A_181))
      | ~ v1_relat_1(k6_relat_1(A_181))
      | ~ r1_tarski(A_181,A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_32])).

tff(c_1357,plain,(
    ! [A_181,A_182] :
      ( k9_relat_1(k6_relat_1(A_181),A_182) = A_181
      | ~ r1_tarski(A_181,A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40,c_1311])).

tff(c_487,plain,(
    ! [A_104] :
      ( k9_relat_1(k6_relat_1(A_104),A_104) = k2_relat_1(k6_relat_1(A_104))
      | ~ v1_relat_1(k6_relat_1(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_475])).

tff(c_491,plain,(
    ! [A_104] : k9_relat_1(k6_relat_1(A_104),A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40,c_487])).

tff(c_547,plain,(
    ! [A_104] : k3_xboole_0(A_104,A_104) = k1_relat_1(k6_relat_1(A_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_535])).

tff(c_552,plain,(
    ! [A_104] : k3_xboole_0(A_104,A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_547])).

tff(c_336,plain,(
    ! [A_62,A_104] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_62),A_104),k6_relat_1(A_104))
      | ~ v1_relat_1(k6_relat_1(A_104))
      | ~ v1_relat_1(k6_relat_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_44])).

tff(c_372,plain,(
    ! [A_62,A_104] : r1_tarski(k7_relat_1(k6_relat_1(A_62),A_104),k6_relat_1(A_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_336])).

tff(c_20203,plain,(
    ! [A_475,A_476] : k3_xboole_0(k7_relat_1(k6_relat_1(A_475),A_476),k6_relat_1(A_476)) = k7_relat_1(k6_relat_1(A_475),A_476) ),
    inference(resolution,[status(thm)],[c_372,c_1372])).

tff(c_1459,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_1372])).

tff(c_20379,plain,(
    ! [A_475,A_476] : k3_xboole_0(k7_relat_1(k6_relat_1(A_475),A_476),k7_relat_1(k6_relat_1(A_475),A_476)) = k3_xboole_0(k7_relat_1(k6_relat_1(A_475),A_476),k6_relat_1(A_476)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20203,c_1459])).

tff(c_20485,plain,(
    ! [A_476,A_475] : k3_xboole_0(k6_relat_1(A_476),k7_relat_1(k6_relat_1(A_475),A_476)) = k7_relat_1(k6_relat_1(A_475),A_476) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_138,c_20379])).

tff(c_1203,plain,(
    ! [A_43,A_174] :
      ( k7_relat_1(k6_relat_1(A_43),A_174) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_370,c_1163])).

tff(c_92393,plain,(
    ! [A_1158,A_1159] : r1_tarski(k7_relat_1(k6_relat_1(A_1158),A_1159),k7_relat_1(k6_relat_1(A_1159),A_1158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_462,c_24,c_462,c_4958,c_38,c_370,c_38,c_92228])).

tff(c_96315,plain,(
    ! [A_1202,A_1203] :
      ( r1_tarski(k6_relat_1(A_1202),k7_relat_1(k6_relat_1(A_1203),A_1202))
      | ~ r1_tarski(A_1202,A_1203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_92393])).

tff(c_1355,plain,(
    ! [A_181,A_182] :
      ( k3_xboole_0(A_181,A_182) = A_181
      | ~ r1_tarski(A_181,A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1308])).

tff(c_96328,plain,(
    ! [A_1202,A_1203] :
      ( k3_xboole_0(k6_relat_1(A_1202),k7_relat_1(k6_relat_1(A_1203),A_1202)) = k6_relat_1(A_1202)
      | ~ r1_tarski(A_1202,A_1203) ) ),
    inference(resolution,[status(thm)],[c_96315,c_1355])).

tff(c_96417,plain,(
    ! [A_1204,A_1205] :
      ( k7_relat_1(k6_relat_1(A_1204),A_1205) = k6_relat_1(A_1205)
      | ~ r1_tarski(A_1205,A_1204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20485,c_96328])).

tff(c_2906,plain,(
    ! [A_230,A_231] : k7_relat_1(k7_relat_1(k6_relat_1(A_230),A_231),A_231) = k7_relat_1(k6_relat_1(A_230),A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_40,c_24,c_370,c_40,c_2667])).

tff(c_2927,plain,(
    ! [A_230,A_231] :
      ( k9_relat_1(k7_relat_1(k6_relat_1(A_230),A_231),A_231) = k2_relat_1(k7_relat_1(k6_relat_1(A_230),A_231))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_230),A_231)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2906,c_32])).

tff(c_2956,plain,(
    ! [A_230,A_231] : k9_relat_1(k7_relat_1(k6_relat_1(A_230),A_231),A_231) = k2_relat_1(k7_relat_1(k6_relat_1(A_230),A_231)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_2927])).

tff(c_17657,plain,(
    ! [A_230,A_231] : k9_relat_1(k7_relat_1(k6_relat_1(A_230),A_231),A_231) = k9_relat_1(k6_relat_1(A_230),A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13760,c_2956])).

tff(c_96852,plain,(
    ! [A_1205,A_1204] :
      ( k9_relat_1(k6_relat_1(A_1205),A_1205) = k9_relat_1(k6_relat_1(A_1204),A_1205)
      | ~ r1_tarski(A_1205,A_1204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96417,c_17657])).

tff(c_97312,plain,(
    ! [A_1206,A_1207] :
      ( k9_relat_1(k6_relat_1(A_1206),A_1207) = A_1207
      | ~ r1_tarski(A_1207,A_1206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_96852])).

tff(c_97666,plain,(
    ! [A_1209,A_1208] :
      ( A_1209 = A_1208
      | ~ r1_tarski(A_1208,A_1209)
      | ~ r1_tarski(A_1209,A_1208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_97312])).

tff(c_97684,plain,(
    ! [A_127,A_1156] :
      ( k7_relat_1(k6_relat_1(A_127),A_1156) = k7_relat_1(k6_relat_1(A_1156),A_127)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_127),A_1156),k7_relat_1(k6_relat_1(A_1156),A_127)) ) ),
    inference(resolution,[status(thm)],[c_92358,c_97666])).

tff(c_98560,plain,(
    ! [A_1214,A_1213] : k7_relat_1(k6_relat_1(A_1214),A_1213) = k7_relat_1(k6_relat_1(A_1213),A_1214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92358,c_97684])).

tff(c_644,plain,(
    ! [B_70,A_69] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_70,A_69)),k2_relat_1(B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_638])).

tff(c_658,plain,(
    ! [B_70,A_69] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_70,A_69)),k2_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_644])).

tff(c_99575,plain,(
    ! [A_1214,A_1213] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_1214),A_1213)),k2_relat_1(k6_relat_1(A_1213)))
      | ~ v1_relat_1(k6_relat_1(A_1213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98560,c_658])).

tff(c_100137,plain,(
    ! [A_1215,A_1216] : r1_tarski(k9_relat_1(k6_relat_1(A_1215),A_1216),A_1216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_13760,c_40,c_99575])).

tff(c_1547,plain,(
    ! [B_189,A_190] : k3_xboole_0(k3_xboole_0(B_189,A_190),A_190) = k3_xboole_0(B_189,A_190) ),
    inference(resolution,[status(thm)],[c_170,c_1372])).

tff(c_1611,plain,(
    ! [A_83,B_189] : k3_xboole_0(A_83,k3_xboole_0(B_189,A_83)) = k3_xboole_0(B_189,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1547])).

tff(c_1845,plain,(
    ! [A_202,B_203] : k3_xboole_0(k3_xboole_0(A_202,B_203),A_202) = k3_xboole_0(B_203,A_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1547])).

tff(c_1958,plain,(
    ! [B_204,A_205] : r1_tarski(k3_xboole_0(B_204,A_205),k3_xboole_0(A_205,B_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1845,c_2])).

tff(c_4195,plain,(
    ! [B_281,A_282] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_281,A_282)),k3_xboole_0(A_282,k1_relat_1(B_281)))
      | ~ v1_relat_1(B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1958])).

tff(c_4234,plain,(
    ! [A_43,A_174] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_43)),k3_xboole_0(A_174,k1_relat_1(k6_relat_1(A_43))))
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ r1_tarski(A_43,A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_4195])).

tff(c_4292,plain,(
    ! [A_283,A_284] :
      ( r1_tarski(A_283,k3_xboole_0(A_284,A_283))
      | ~ r1_tarski(A_283,A_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38,c_38,c_4234])).

tff(c_4295,plain,(
    ! [A_283,A_284] :
      ( k3_xboole_0(A_283,k3_xboole_0(A_284,A_283)) = A_283
      | ~ r1_tarski(A_283,A_284) ) ),
    inference(resolution,[status(thm)],[c_4292,c_1355])).

tff(c_4364,plain,(
    ! [A_284,A_283] :
      ( k3_xboole_0(A_284,A_283) = A_283
      | ~ r1_tarski(A_283,A_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_4295])).

tff(c_100189,plain,(
    ! [A_1216,A_1215] : k3_xboole_0(A_1216,k9_relat_1(k6_relat_1(A_1215),A_1216)) = k9_relat_1(k6_relat_1(A_1215),A_1216) ),
    inference(resolution,[status(thm)],[c_100137,c_4364])).

tff(c_100269,plain,(
    ! [A_1215,A_1216] : k9_relat_1(k6_relat_1(A_1215),A_1216) = k3_xboole_0(A_1215,A_1216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33731,c_100189])).

tff(c_717,plain,(
    ! [A_152,A_61] :
      ( k5_relat_1(k6_relat_1(A_152),k6_relat_1(A_61)) = k6_relat_1(A_61)
      | ~ r1_tarski(A_61,A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_710])).

tff(c_1244,plain,(
    ! [A_152,A_178,A_61] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_152),A_178),k6_relat_1(A_61)) = k7_relat_1(k6_relat_1(A_61),A_178)
      | ~ v1_relat_1(k6_relat_1(A_61))
      | ~ v1_relat_1(k6_relat_1(A_152))
      | ~ r1_tarski(A_61,A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_1209])).

tff(c_44516,plain,(
    ! [A_693,A_694,A_695] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_693),A_694),k6_relat_1(A_695)) = k7_relat_1(k6_relat_1(A_695),A_694)
      | ~ r1_tarski(A_695,A_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_1244])).

tff(c_44729,plain,(
    ! [A_693,A_694] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_693),A_694))),A_694) = k7_relat_1(k6_relat_1(A_693),A_694)
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_693),A_694)),A_693)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_693),A_694)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_44516])).

tff(c_44821,plain,(
    ! [A_693,A_694] : k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_693),A_694)),A_694) = k7_relat_1(k6_relat_1(A_693),A_694) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_687,c_13760,c_13760,c_44729])).

tff(c_144218,plain,(
    ! [A_1583,A_1584] : k7_relat_1(k6_relat_1(k3_xboole_0(A_1583,A_1584)),A_1584) = k7_relat_1(k6_relat_1(A_1583),A_1584) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100269,c_44821])).

tff(c_144915,plain,(
    ! [A_1583,A_1584] :
      ( k7_relat_1(k6_relat_1(A_1583),A_1584) = k6_relat_1(k3_xboole_0(A_1583,A_1584))
      | ~ r1_tarski(k3_xboole_0(A_1583,A_1584),A_1584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144218,c_1203])).

tff(c_145410,plain,(
    ! [A_1583,A_1584] : k7_relat_1(k6_relat_1(A_1583),A_1584) = k6_relat_1(k3_xboole_0(A_1583,A_1584)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_144915])).

tff(c_54,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_353,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_54])).

tff(c_380,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_353])).

tff(c_145618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145410,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.71/26.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.71/26.32  
% 35.71/26.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.71/26.32  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 35.71/26.32  
% 35.71/26.32  %Foreground sorts:
% 35.71/26.32  
% 35.71/26.32  
% 35.71/26.32  %Background operators:
% 35.71/26.32  
% 35.71/26.32  
% 35.71/26.32  %Foreground operators:
% 35.71/26.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 35.71/26.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.71/26.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 35.71/26.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 35.71/26.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 35.71/26.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 35.71/26.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.71/26.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 35.71/26.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 35.71/26.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 35.71/26.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 35.71/26.32  tff('#skF_2', type, '#skF_2': $i).
% 35.71/26.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 35.71/26.32  tff('#skF_1', type, '#skF_1': $i).
% 35.71/26.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 35.71/26.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 35.71/26.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.71/26.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 35.71/26.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 35.71/26.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.71/26.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 35.71/26.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 35.71/26.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 35.71/26.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 35.71/26.32  
% 35.71/26.35  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 35.71/26.35  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 35.71/26.35  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 35.71/26.35  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 35.71/26.35  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 35.71/26.35  tff(f_120, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 35.71/26.35  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 35.71/26.35  tff(f_96, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 35.71/26.35  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 35.71/26.35  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 35.71/26.35  tff(f_116, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 35.71/26.35  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 35.71/26.35  tff(f_112, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 35.71/26.35  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 35.71/26.35  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 35.71/26.35  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 35.71/26.35  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 35.71/26.35  tff(f_123, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 35.71/26.35  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 35.71/26.35  tff(c_108, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 35.71/26.35  tff(c_132, plain, (![B_82, A_83]: (k1_setfam_1(k2_tarski(B_82, A_83))=k3_xboole_0(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_6, c_108])).
% 35.71/26.35  tff(c_20, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 35.71/26.35  tff(c_155, plain, (![B_84, A_85]: (k3_xboole_0(B_84, A_85)=k3_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_132, c_20])).
% 35.71/26.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 35.71/26.35  tff(c_170, plain, (![B_84, A_85]: (r1_tarski(k3_xboole_0(B_84, A_85), A_85))), inference(superposition, [status(thm), theory('equality')], [c_155, c_2])).
% 35.71/26.35  tff(c_138, plain, (![B_82, A_83]: (k3_xboole_0(B_82, A_83)=k3_xboole_0(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_132, c_20])).
% 35.71/26.35  tff(c_24, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 35.71/26.35  tff(c_32, plain, (![B_50, A_49]: (k2_relat_1(k7_relat_1(B_50, A_49))=k9_relat_1(B_50, A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 35.71/26.35  tff(c_325, plain, (![A_104, B_105]: (k5_relat_1(k6_relat_1(A_104), B_105)=k7_relat_1(B_105, A_104) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_120])).
% 35.71/26.35  tff(c_28, plain, (![B_44, A_43]: (k5_relat_1(B_44, k6_relat_1(A_43))=k8_relat_1(A_43, B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 35.71/26.35  tff(c_332, plain, (![A_43, A_104]: (k8_relat_1(A_43, k6_relat_1(A_104))=k7_relat_1(k6_relat_1(A_43), A_104) | ~v1_relat_1(k6_relat_1(A_104)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_325, c_28])).
% 35.71/26.35  tff(c_370, plain, (![A_43, A_104]: (k8_relat_1(A_43, k6_relat_1(A_104))=k7_relat_1(k6_relat_1(A_43), A_104))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_332])).
% 35.71/26.35  tff(c_40, plain, (![A_61]: (k2_relat_1(k6_relat_1(A_61))=A_61)), inference(cnfTransformation, [status(thm)], [f_96])).
% 35.71/26.35  tff(c_638, plain, (![A_144, B_145]: (r1_tarski(k2_relat_1(k5_relat_1(A_144, B_145)), k2_relat_1(B_145)) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_82])).
% 35.71/26.35  tff(c_647, plain, (![A_43, B_44]: (r1_tarski(k2_relat_1(k8_relat_1(A_43, B_44)), k2_relat_1(k6_relat_1(A_43))) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_28, c_638])).
% 35.71/26.35  tff(c_667, plain, (![A_146, B_147]: (r1_tarski(k2_relat_1(k8_relat_1(A_146, B_147)), A_146) | ~v1_relat_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40, c_647])).
% 35.71/26.35  tff(c_670, plain, (![A_43, A_104]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_43), A_104)), A_43) | ~v1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_370, c_667])).
% 35.71/26.35  tff(c_678, plain, (![A_148, A_149]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_148), A_149)), A_148))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_670])).
% 35.71/26.35  tff(c_682, plain, (![A_148, A_49]: (r1_tarski(k9_relat_1(k6_relat_1(A_148), A_49), A_148) | ~v1_relat_1(k6_relat_1(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_678])).
% 35.71/26.35  tff(c_687, plain, (![A_148, A_49]: (r1_tarski(k9_relat_1(k6_relat_1(A_148), A_49), A_148))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_682])).
% 35.71/26.35  tff(c_38, plain, (![A_61]: (k1_relat_1(k6_relat_1(A_61))=A_61)), inference(cnfTransformation, [status(thm)], [f_96])).
% 35.71/26.35  tff(c_694, plain, (![A_152, B_153]: (k5_relat_1(k6_relat_1(A_152), B_153)=B_153 | ~r1_tarski(k1_relat_1(B_153), A_152) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_108])).
% 35.71/26.35  tff(c_710, plain, (![A_152, A_61]: (k5_relat_1(k6_relat_1(A_152), k6_relat_1(A_61))=k6_relat_1(A_61) | ~r1_tarski(A_61, A_152) | ~v1_relat_1(k6_relat_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_694])).
% 35.71/26.35  tff(c_1106, plain, (![A_174, A_175]: (k5_relat_1(k6_relat_1(A_174), k6_relat_1(A_175))=k6_relat_1(A_175) | ~r1_tarski(A_175, A_174))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_710])).
% 35.71/26.35  tff(c_1163, plain, (![A_43, A_174]: (k8_relat_1(A_43, k6_relat_1(A_174))=k6_relat_1(A_43) | ~r1_tarski(A_43, A_174) | ~v1_relat_1(k6_relat_1(A_174)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1106])).
% 35.71/26.35  tff(c_1279, plain, (![A_181, A_182]: (k7_relat_1(k6_relat_1(A_181), A_182)=k6_relat_1(A_181) | ~r1_tarski(A_181, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_370, c_1163])).
% 35.71/26.35  tff(c_501, plain, (![B_126, A_127]: (k3_xboole_0(k1_relat_1(B_126), A_127)=k1_relat_1(k7_relat_1(B_126, A_127)) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_116])).
% 35.71/26.35  tff(c_530, plain, (![A_61, A_127]: (k1_relat_1(k7_relat_1(k6_relat_1(A_61), A_127))=k3_xboole_0(A_61, A_127) | ~v1_relat_1(k6_relat_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_501])).
% 35.71/26.35  tff(c_534, plain, (![A_61, A_127]: (k1_relat_1(k7_relat_1(k6_relat_1(A_61), A_127))=k3_xboole_0(A_61, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_530])).
% 35.71/26.35  tff(c_1308, plain, (![A_181, A_182]: (k3_xboole_0(A_181, A_182)=k1_relat_1(k6_relat_1(A_181)) | ~r1_tarski(A_181, A_182))), inference(superposition, [status(thm), theory('equality')], [c_1279, c_534])).
% 35.71/26.35  tff(c_1372, plain, (![A_183, A_184]: (k3_xboole_0(A_183, A_184)=A_183 | ~r1_tarski(A_183, A_184))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1308])).
% 35.71/26.35  tff(c_3305, plain, (![A_243, A_244]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_243), A_244), A_243)=k9_relat_1(k6_relat_1(A_243), A_244))), inference(resolution, [status(thm)], [c_687, c_1372])).
% 35.71/26.35  tff(c_3381, plain, (![A_83, A_244]: (k3_xboole_0(A_83, k9_relat_1(k6_relat_1(A_83), A_244))=k9_relat_1(k6_relat_1(A_83), A_244))), inference(superposition, [status(thm), theory('equality')], [c_138, c_3305])).
% 35.71/26.35  tff(c_442, plain, (![A_117, A_118]: (k8_relat_1(A_117, k6_relat_1(A_118))=k7_relat_1(k6_relat_1(A_117), A_118))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_332])).
% 35.71/26.35  tff(c_278, plain, (![B_100, A_101]: (k5_relat_1(B_100, k6_relat_1(A_101))=k8_relat_1(A_101, B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_64])).
% 35.71/26.35  tff(c_22, plain, (![A_36, B_37]: (v1_relat_1(k5_relat_1(A_36, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 35.71/26.35  tff(c_287, plain, (![A_101, B_100]: (v1_relat_1(k8_relat_1(A_101, B_100)) | ~v1_relat_1(k6_relat_1(A_101)) | ~v1_relat_1(B_100) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_278, c_22])).
% 35.71/26.35  tff(c_314, plain, (![A_101, B_100]: (v1_relat_1(k8_relat_1(A_101, B_100)) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_287])).
% 35.71/26.35  tff(c_452, plain, (![A_117, A_118]: (v1_relat_1(k7_relat_1(k6_relat_1(A_117), A_118)) | ~v1_relat_1(k6_relat_1(A_118)))), inference(superposition, [status(thm), theory('equality')], [c_442, c_314])).
% 35.71/26.35  tff(c_462, plain, (![A_117, A_118]: (v1_relat_1(k7_relat_1(k6_relat_1(A_117), A_118)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_452])).
% 35.71/26.35  tff(c_475, plain, (![B_123, A_124]: (k2_relat_1(k7_relat_1(B_123, A_124))=k9_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_75])).
% 35.71/26.35  tff(c_48, plain, (![A_66]: (k5_relat_1(A_66, k6_relat_1(k2_relat_1(A_66)))=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_112])).
% 35.71/26.35  tff(c_8050, plain, (![B_329, A_330]: (k5_relat_1(k7_relat_1(B_329, A_330), k6_relat_1(k9_relat_1(B_329, A_330)))=k7_relat_1(B_329, A_330) | ~v1_relat_1(k7_relat_1(B_329, A_330)) | ~v1_relat_1(B_329))), inference(superposition, [status(thm), theory('equality')], [c_475, c_48])).
% 35.71/26.35  tff(c_52, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=k7_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_120])).
% 35.71/26.35  tff(c_1209, plain, (![B_176, C_177, A_178]: (k7_relat_1(k5_relat_1(B_176, C_177), A_178)=k5_relat_1(k7_relat_1(B_176, A_178), C_177) | ~v1_relat_1(C_177) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_60])).
% 35.71/26.35  tff(c_1254, plain, (![A_69, A_178, B_70]: (k5_relat_1(k7_relat_1(k6_relat_1(A_69), A_178), B_70)=k7_relat_1(k7_relat_1(B_70, A_69), A_178) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1209])).
% 35.71/26.35  tff(c_1271, plain, (![A_69, A_178, B_70]: (k5_relat_1(k7_relat_1(k6_relat_1(A_69), A_178), B_70)=k7_relat_1(k7_relat_1(B_70, A_69), A_178) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1254])).
% 35.71/26.35  tff(c_8063, plain, (![A_69, A_330]: (k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_69), A_330)), A_69), A_330)=k7_relat_1(k6_relat_1(A_69), A_330) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_69), A_330))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_69), A_330)) | ~v1_relat_1(k6_relat_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_8050, c_1271])).
% 35.71/26.35  tff(c_33550, plain, (![A_604, A_605]: (k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_604), A_605)), A_604), A_605)=k7_relat_1(k6_relat_1(A_604), A_605))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_462, c_24, c_8063])).
% 35.71/26.35  tff(c_535, plain, (![A_128, A_129]: (k1_relat_1(k7_relat_1(k6_relat_1(A_128), A_129))=k3_xboole_0(A_128, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_530])).
% 35.71/26.35  tff(c_50, plain, (![B_68, A_67]: (k3_xboole_0(k1_relat_1(B_68), A_67)=k1_relat_1(k7_relat_1(B_68, A_67)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_116])).
% 35.71/26.35  tff(c_541, plain, (![A_128, A_129, A_67]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_128), A_129), A_67))=k3_xboole_0(k3_xboole_0(A_128, A_129), A_67) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_128), A_129)))), inference(superposition, [status(thm), theory('equality')], [c_535, c_50])).
% 35.71/26.35  tff(c_550, plain, (![A_128, A_129, A_67]: (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_128), A_129), A_67))=k3_xboole_0(k3_xboole_0(A_128, A_129), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_541])).
% 35.71/26.35  tff(c_33576, plain, (![A_604, A_605]: (k3_xboole_0(k3_xboole_0(k9_relat_1(k6_relat_1(A_604), A_605), A_604), A_605)=k1_relat_1(k7_relat_1(k6_relat_1(A_604), A_605)))), inference(superposition, [status(thm), theory('equality')], [c_33550, c_550])).
% 35.71/26.35  tff(c_33731, plain, (![A_605, A_604]: (k3_xboole_0(A_605, k9_relat_1(k6_relat_1(A_604), A_605))=k3_xboole_0(A_604, A_605))), inference(demodulation, [status(thm), theory('equality')], [c_3381, c_534, c_138, c_138, c_33576])).
% 35.71/26.35  tff(c_205, plain, (![A_88]: (k5_relat_1(A_88, k6_relat_1(k2_relat_1(A_88)))=A_88 | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_112])).
% 35.71/26.35  tff(c_214, plain, (![A_61]: (k5_relat_1(k6_relat_1(A_61), k6_relat_1(A_61))=k6_relat_1(A_61) | ~v1_relat_1(k6_relat_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_205])).
% 35.71/26.35  tff(c_218, plain, (![A_61]: (k5_relat_1(k6_relat_1(A_61), k6_relat_1(A_61))=k6_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_214])).
% 35.71/26.35  tff(c_1263, plain, (![A_66, A_178]: (k5_relat_1(k7_relat_1(A_66, A_178), k6_relat_1(k2_relat_1(A_66)))=k7_relat_1(A_66, A_178) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_66))) | ~v1_relat_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1209])).
% 35.71/26.35  tff(c_2835, plain, (![A_228, A_229]: (k5_relat_1(k7_relat_1(A_228, A_229), k6_relat_1(k2_relat_1(A_228)))=k7_relat_1(A_228, A_229) | ~v1_relat_1(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1263])).
% 35.71/26.35  tff(c_2886, plain, (![A_61, A_229]: (k5_relat_1(k7_relat_1(k6_relat_1(A_61), A_229), k6_relat_1(A_61))=k7_relat_1(k6_relat_1(A_61), A_229) | ~v1_relat_1(k6_relat_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2835])).
% 35.71/26.35  tff(c_13640, plain, (![A_385, A_386]: (k5_relat_1(k7_relat_1(k6_relat_1(A_385), A_386), k6_relat_1(A_385))=k7_relat_1(k6_relat_1(A_385), A_386))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2886])).
% 35.71/26.35  tff(c_1235, plain, (![B_176, A_178, C_177]: (k2_relat_1(k5_relat_1(k7_relat_1(B_176, A_178), C_177))=k9_relat_1(k5_relat_1(B_176, C_177), A_178) | ~v1_relat_1(k5_relat_1(B_176, C_177)) | ~v1_relat_1(C_177) | ~v1_relat_1(B_176))), inference(superposition, [status(thm), theory('equality')], [c_1209, c_32])).
% 35.71/26.35  tff(c_13652, plain, (![A_385, A_386]: (k9_relat_1(k5_relat_1(k6_relat_1(A_385), k6_relat_1(A_385)), A_386)=k2_relat_1(k7_relat_1(k6_relat_1(A_385), A_386)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_385), k6_relat_1(A_385))) | ~v1_relat_1(k6_relat_1(A_385)) | ~v1_relat_1(k6_relat_1(A_385)))), inference(superposition, [status(thm), theory('equality')], [c_13640, c_1235])).
% 35.71/26.35  tff(c_13760, plain, (![A_385, A_386]: (k2_relat_1(k7_relat_1(k6_relat_1(A_385), A_386))=k9_relat_1(k6_relat_1(A_385), A_386))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_24, c_218, c_218, c_13652])).
% 35.71/26.35  tff(c_1002, plain, (![A_167, B_168, C_169]: (k8_relat_1(A_167, k5_relat_1(B_168, C_169))=k5_relat_1(B_168, k8_relat_1(A_167, C_169)) | ~v1_relat_1(C_169) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_71])).
% 35.71/26.35  tff(c_1040, plain, (![A_66, A_167]: (k5_relat_1(A_66, k8_relat_1(A_167, k6_relat_1(k2_relat_1(A_66))))=k8_relat_1(A_167, A_66) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_66))) | ~v1_relat_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1002])).
% 35.71/26.35  tff(c_2615, plain, (![A_224, A_225]: (k5_relat_1(A_224, k7_relat_1(k6_relat_1(A_225), k2_relat_1(A_224)))=k8_relat_1(A_225, A_224) | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_370, c_1040])).
% 35.71/26.35  tff(c_2667, plain, (![A_225, A_69]: (k7_relat_1(k7_relat_1(k6_relat_1(A_225), k2_relat_1(k6_relat_1(A_69))), A_69)=k8_relat_1(A_225, k6_relat_1(A_69)) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_225), k2_relat_1(k6_relat_1(A_69)))))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2615])).
% 35.71/26.35  tff(c_2692, plain, (![A_225, A_69]: (k7_relat_1(k7_relat_1(k6_relat_1(A_225), A_69), A_69)=k7_relat_1(k6_relat_1(A_225), A_69))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_40, c_24, c_370, c_40, c_2667])).
% 35.71/26.35  tff(c_350, plain, (![A_104]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_104))), A_104)=k6_relat_1(A_104) | ~v1_relat_1(k6_relat_1(A_104)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_104)))))), inference(superposition, [status(thm), theory('equality')], [c_325, c_48])).
% 35.71/26.35  tff(c_378, plain, (![A_104]: (k7_relat_1(k6_relat_1(A_104), A_104)=k6_relat_1(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_40, c_350])).
% 35.71/26.35  tff(c_1257, plain, (![B_44, A_178, A_43]: (k5_relat_1(k7_relat_1(B_44, A_178), k6_relat_1(A_43))=k7_relat_1(k8_relat_1(A_43, B_44), A_178) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1209])).
% 35.71/26.35  tff(c_4864, plain, (![B_291, A_292, A_293]: (k5_relat_1(k7_relat_1(B_291, A_292), k6_relat_1(A_293))=k7_relat_1(k8_relat_1(A_293, B_291), A_292) | ~v1_relat_1(B_291))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1257])).
% 35.71/26.35  tff(c_4928, plain, (![A_293, A_104]: (k7_relat_1(k8_relat_1(A_293, k6_relat_1(A_104)), A_104)=k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_293)) | ~v1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_4864])).
% 35.71/26.35  tff(c_4958, plain, (![A_104, A_293]: (k5_relat_1(k6_relat_1(A_104), k6_relat_1(A_293))=k7_relat_1(k6_relat_1(A_293), A_104))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2692, c_370, c_4928])).
% 35.71/26.35  tff(c_516, plain, (![B_126, A_127]: (r1_tarski(k1_relat_1(k7_relat_1(B_126, A_127)), k1_relat_1(B_126)) | ~v1_relat_1(B_126))), inference(superposition, [status(thm), theory('equality')], [c_501, c_2])).
% 35.71/26.35  tff(c_711, plain, (![B_126, A_127]: (k5_relat_1(k6_relat_1(k1_relat_1(B_126)), k7_relat_1(B_126, A_127))=k7_relat_1(B_126, A_127) | ~v1_relat_1(k7_relat_1(B_126, A_127)) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_516, c_694])).
% 35.71/26.35  tff(c_2192, plain, (![A_208, B_209, C_210]: (k5_relat_1(k5_relat_1(A_208, B_209), C_210)=k5_relat_1(A_208, k5_relat_1(B_209, C_210)) | ~v1_relat_1(C_210) | ~v1_relat_1(B_209) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_92])).
% 35.71/26.35  tff(c_44, plain, (![B_63, A_62]: (r1_tarski(k5_relat_1(B_63, k6_relat_1(A_62)), B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_102])).
% 35.71/26.35  tff(c_2219, plain, (![A_208, B_209, A_62]: (r1_tarski(k5_relat_1(A_208, k5_relat_1(B_209, k6_relat_1(A_62))), k5_relat_1(A_208, B_209)) | ~v1_relat_1(k5_relat_1(A_208, B_209)) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(B_209) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_2192, c_44])).
% 35.71/26.35  tff(c_8718, plain, (![A_335, B_336, A_337]: (r1_tarski(k5_relat_1(A_335, k5_relat_1(B_336, k6_relat_1(A_337))), k5_relat_1(A_335, B_336)) | ~v1_relat_1(k5_relat_1(A_335, B_336)) | ~v1_relat_1(B_336) | ~v1_relat_1(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2219])).
% 35.71/26.35  tff(c_8838, plain, (![B_44, A_43, A_337]: (r1_tarski(k5_relat_1(B_44, k5_relat_1(k6_relat_1(A_43), k6_relat_1(A_337))), k8_relat_1(A_43, B_44)) | ~v1_relat_1(k5_relat_1(B_44, k6_relat_1(A_43))) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8718])).
% 35.71/26.35  tff(c_92188, plain, (![B_1155, A_1156, A_1157]: (r1_tarski(k5_relat_1(B_1155, k7_relat_1(k6_relat_1(A_1156), A_1157)), k8_relat_1(A_1157, B_1155)) | ~v1_relat_1(k5_relat_1(B_1155, k6_relat_1(A_1157))) | ~v1_relat_1(B_1155))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4958, c_8838])).
% 35.71/26.35  tff(c_92228, plain, (![A_1156, A_127]: (r1_tarski(k7_relat_1(k6_relat_1(A_1156), A_127), k8_relat_1(A_127, k6_relat_1(k1_relat_1(k6_relat_1(A_1156))))) | ~v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_1156))), k6_relat_1(A_127))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_1156)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_1156), A_127)) | ~v1_relat_1(k6_relat_1(A_1156)))), inference(superposition, [status(thm), theory('equality')], [c_711, c_92188])).
% 35.71/26.35  tff(c_92358, plain, (![A_1156, A_127]: (r1_tarski(k7_relat_1(k6_relat_1(A_1156), A_127), k7_relat_1(k6_relat_1(A_127), A_1156)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_462, c_24, c_462, c_4958, c_38, c_370, c_38, c_92228])).
% 35.71/26.35  tff(c_1311, plain, (![A_181, A_182]: (k9_relat_1(k6_relat_1(A_181), A_182)=k2_relat_1(k6_relat_1(A_181)) | ~v1_relat_1(k6_relat_1(A_181)) | ~r1_tarski(A_181, A_182))), inference(superposition, [status(thm), theory('equality')], [c_1279, c_32])).
% 35.71/26.35  tff(c_1357, plain, (![A_181, A_182]: (k9_relat_1(k6_relat_1(A_181), A_182)=A_181 | ~r1_tarski(A_181, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40, c_1311])).
% 35.71/26.35  tff(c_487, plain, (![A_104]: (k9_relat_1(k6_relat_1(A_104), A_104)=k2_relat_1(k6_relat_1(A_104)) | ~v1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_475])).
% 35.71/26.35  tff(c_491, plain, (![A_104]: (k9_relat_1(k6_relat_1(A_104), A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40, c_487])).
% 35.71/26.35  tff(c_547, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=k1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_535])).
% 35.71/26.35  tff(c_552, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_547])).
% 35.71/26.35  tff(c_336, plain, (![A_62, A_104]: (r1_tarski(k7_relat_1(k6_relat_1(A_62), A_104), k6_relat_1(A_104)) | ~v1_relat_1(k6_relat_1(A_104)) | ~v1_relat_1(k6_relat_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_325, c_44])).
% 35.71/26.35  tff(c_372, plain, (![A_62, A_104]: (r1_tarski(k7_relat_1(k6_relat_1(A_62), A_104), k6_relat_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_336])).
% 35.71/26.35  tff(c_20203, plain, (![A_475, A_476]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_475), A_476), k6_relat_1(A_476))=k7_relat_1(k6_relat_1(A_475), A_476))), inference(resolution, [status(thm)], [c_372, c_1372])).
% 35.71/26.35  tff(c_1459, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_1372])).
% 35.71/26.35  tff(c_20379, plain, (![A_475, A_476]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_475), A_476), k7_relat_1(k6_relat_1(A_475), A_476))=k3_xboole_0(k7_relat_1(k6_relat_1(A_475), A_476), k6_relat_1(A_476)))), inference(superposition, [status(thm), theory('equality')], [c_20203, c_1459])).
% 35.71/26.35  tff(c_20485, plain, (![A_476, A_475]: (k3_xboole_0(k6_relat_1(A_476), k7_relat_1(k6_relat_1(A_475), A_476))=k7_relat_1(k6_relat_1(A_475), A_476))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_138, c_20379])).
% 35.71/26.35  tff(c_1203, plain, (![A_43, A_174]: (k7_relat_1(k6_relat_1(A_43), A_174)=k6_relat_1(A_43) | ~r1_tarski(A_43, A_174))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_370, c_1163])).
% 35.71/26.35  tff(c_92393, plain, (![A_1158, A_1159]: (r1_tarski(k7_relat_1(k6_relat_1(A_1158), A_1159), k7_relat_1(k6_relat_1(A_1159), A_1158)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_462, c_24, c_462, c_4958, c_38, c_370, c_38, c_92228])).
% 35.71/26.35  tff(c_96315, plain, (![A_1202, A_1203]: (r1_tarski(k6_relat_1(A_1202), k7_relat_1(k6_relat_1(A_1203), A_1202)) | ~r1_tarski(A_1202, A_1203))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_92393])).
% 35.71/26.35  tff(c_1355, plain, (![A_181, A_182]: (k3_xboole_0(A_181, A_182)=A_181 | ~r1_tarski(A_181, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1308])).
% 35.71/26.35  tff(c_96328, plain, (![A_1202, A_1203]: (k3_xboole_0(k6_relat_1(A_1202), k7_relat_1(k6_relat_1(A_1203), A_1202))=k6_relat_1(A_1202) | ~r1_tarski(A_1202, A_1203))), inference(resolution, [status(thm)], [c_96315, c_1355])).
% 35.71/26.35  tff(c_96417, plain, (![A_1204, A_1205]: (k7_relat_1(k6_relat_1(A_1204), A_1205)=k6_relat_1(A_1205) | ~r1_tarski(A_1205, A_1204))), inference(demodulation, [status(thm), theory('equality')], [c_20485, c_96328])).
% 35.71/26.35  tff(c_2906, plain, (![A_230, A_231]: (k7_relat_1(k7_relat_1(k6_relat_1(A_230), A_231), A_231)=k7_relat_1(k6_relat_1(A_230), A_231))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_40, c_24, c_370, c_40, c_2667])).
% 35.71/26.35  tff(c_2927, plain, (![A_230, A_231]: (k9_relat_1(k7_relat_1(k6_relat_1(A_230), A_231), A_231)=k2_relat_1(k7_relat_1(k6_relat_1(A_230), A_231)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_230), A_231)))), inference(superposition, [status(thm), theory('equality')], [c_2906, c_32])).
% 35.71/26.35  tff(c_2956, plain, (![A_230, A_231]: (k9_relat_1(k7_relat_1(k6_relat_1(A_230), A_231), A_231)=k2_relat_1(k7_relat_1(k6_relat_1(A_230), A_231)))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_2927])).
% 35.71/26.35  tff(c_17657, plain, (![A_230, A_231]: (k9_relat_1(k7_relat_1(k6_relat_1(A_230), A_231), A_231)=k9_relat_1(k6_relat_1(A_230), A_231))), inference(demodulation, [status(thm), theory('equality')], [c_13760, c_2956])).
% 35.71/26.35  tff(c_96852, plain, (![A_1205, A_1204]: (k9_relat_1(k6_relat_1(A_1205), A_1205)=k9_relat_1(k6_relat_1(A_1204), A_1205) | ~r1_tarski(A_1205, A_1204))), inference(superposition, [status(thm), theory('equality')], [c_96417, c_17657])).
% 35.71/26.35  tff(c_97312, plain, (![A_1206, A_1207]: (k9_relat_1(k6_relat_1(A_1206), A_1207)=A_1207 | ~r1_tarski(A_1207, A_1206))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_96852])).
% 35.71/26.35  tff(c_97666, plain, (![A_1209, A_1208]: (A_1209=A_1208 | ~r1_tarski(A_1208, A_1209) | ~r1_tarski(A_1209, A_1208))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_97312])).
% 35.71/26.35  tff(c_97684, plain, (![A_127, A_1156]: (k7_relat_1(k6_relat_1(A_127), A_1156)=k7_relat_1(k6_relat_1(A_1156), A_127) | ~r1_tarski(k7_relat_1(k6_relat_1(A_127), A_1156), k7_relat_1(k6_relat_1(A_1156), A_127)))), inference(resolution, [status(thm)], [c_92358, c_97666])).
% 35.71/26.35  tff(c_98560, plain, (![A_1214, A_1213]: (k7_relat_1(k6_relat_1(A_1214), A_1213)=k7_relat_1(k6_relat_1(A_1213), A_1214))), inference(demodulation, [status(thm), theory('equality')], [c_92358, c_97684])).
% 35.71/26.35  tff(c_644, plain, (![B_70, A_69]: (r1_tarski(k2_relat_1(k7_relat_1(B_70, A_69)), k2_relat_1(B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_52, c_638])).
% 35.71/26.35  tff(c_658, plain, (![B_70, A_69]: (r1_tarski(k2_relat_1(k7_relat_1(B_70, A_69)), k2_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_644])).
% 35.71/26.35  tff(c_99575, plain, (![A_1214, A_1213]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_1214), A_1213)), k2_relat_1(k6_relat_1(A_1213))) | ~v1_relat_1(k6_relat_1(A_1213)))), inference(superposition, [status(thm), theory('equality')], [c_98560, c_658])).
% 35.71/26.35  tff(c_100137, plain, (![A_1215, A_1216]: (r1_tarski(k9_relat_1(k6_relat_1(A_1215), A_1216), A_1216))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_13760, c_40, c_99575])).
% 35.71/26.35  tff(c_1547, plain, (![B_189, A_190]: (k3_xboole_0(k3_xboole_0(B_189, A_190), A_190)=k3_xboole_0(B_189, A_190))), inference(resolution, [status(thm)], [c_170, c_1372])).
% 35.71/26.35  tff(c_1611, plain, (![A_83, B_189]: (k3_xboole_0(A_83, k3_xboole_0(B_189, A_83))=k3_xboole_0(B_189, A_83))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1547])).
% 35.71/26.35  tff(c_1845, plain, (![A_202, B_203]: (k3_xboole_0(k3_xboole_0(A_202, B_203), A_202)=k3_xboole_0(B_203, A_202))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1547])).
% 35.71/26.35  tff(c_1958, plain, (![B_204, A_205]: (r1_tarski(k3_xboole_0(B_204, A_205), k3_xboole_0(A_205, B_204)))), inference(superposition, [status(thm), theory('equality')], [c_1845, c_2])).
% 35.71/26.35  tff(c_4195, plain, (![B_281, A_282]: (r1_tarski(k1_relat_1(k7_relat_1(B_281, A_282)), k3_xboole_0(A_282, k1_relat_1(B_281))) | ~v1_relat_1(B_281))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1958])).
% 35.71/26.35  tff(c_4234, plain, (![A_43, A_174]: (r1_tarski(k1_relat_1(k6_relat_1(A_43)), k3_xboole_0(A_174, k1_relat_1(k6_relat_1(A_43)))) | ~v1_relat_1(k6_relat_1(A_43)) | ~r1_tarski(A_43, A_174))), inference(superposition, [status(thm), theory('equality')], [c_1203, c_4195])).
% 35.71/26.35  tff(c_4292, plain, (![A_283, A_284]: (r1_tarski(A_283, k3_xboole_0(A_284, A_283)) | ~r1_tarski(A_283, A_284))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38, c_38, c_4234])).
% 35.71/26.35  tff(c_4295, plain, (![A_283, A_284]: (k3_xboole_0(A_283, k3_xboole_0(A_284, A_283))=A_283 | ~r1_tarski(A_283, A_284))), inference(resolution, [status(thm)], [c_4292, c_1355])).
% 35.71/26.35  tff(c_4364, plain, (![A_284, A_283]: (k3_xboole_0(A_284, A_283)=A_283 | ~r1_tarski(A_283, A_284))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_4295])).
% 35.71/26.35  tff(c_100189, plain, (![A_1216, A_1215]: (k3_xboole_0(A_1216, k9_relat_1(k6_relat_1(A_1215), A_1216))=k9_relat_1(k6_relat_1(A_1215), A_1216))), inference(resolution, [status(thm)], [c_100137, c_4364])).
% 35.71/26.35  tff(c_100269, plain, (![A_1215, A_1216]: (k9_relat_1(k6_relat_1(A_1215), A_1216)=k3_xboole_0(A_1215, A_1216))), inference(demodulation, [status(thm), theory('equality')], [c_33731, c_100189])).
% 35.71/26.35  tff(c_717, plain, (![A_152, A_61]: (k5_relat_1(k6_relat_1(A_152), k6_relat_1(A_61))=k6_relat_1(A_61) | ~r1_tarski(A_61, A_152))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_710])).
% 35.71/26.35  tff(c_1244, plain, (![A_152, A_178, A_61]: (k5_relat_1(k7_relat_1(k6_relat_1(A_152), A_178), k6_relat_1(A_61))=k7_relat_1(k6_relat_1(A_61), A_178) | ~v1_relat_1(k6_relat_1(A_61)) | ~v1_relat_1(k6_relat_1(A_152)) | ~r1_tarski(A_61, A_152))), inference(superposition, [status(thm), theory('equality')], [c_717, c_1209])).
% 35.71/26.35  tff(c_44516, plain, (![A_693, A_694, A_695]: (k5_relat_1(k7_relat_1(k6_relat_1(A_693), A_694), k6_relat_1(A_695))=k7_relat_1(k6_relat_1(A_695), A_694) | ~r1_tarski(A_695, A_693))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_1244])).
% 35.71/26.35  tff(c_44729, plain, (![A_693, A_694]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_693), A_694))), A_694)=k7_relat_1(k6_relat_1(A_693), A_694) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_693), A_694)), A_693) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_693), A_694)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_44516])).
% 35.71/26.35  tff(c_44821, plain, (![A_693, A_694]: (k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_693), A_694)), A_694)=k7_relat_1(k6_relat_1(A_693), A_694))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_687, c_13760, c_13760, c_44729])).
% 35.71/26.35  tff(c_144218, plain, (![A_1583, A_1584]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1583, A_1584)), A_1584)=k7_relat_1(k6_relat_1(A_1583), A_1584))), inference(demodulation, [status(thm), theory('equality')], [c_100269, c_44821])).
% 35.71/26.35  tff(c_144915, plain, (![A_1583, A_1584]: (k7_relat_1(k6_relat_1(A_1583), A_1584)=k6_relat_1(k3_xboole_0(A_1583, A_1584)) | ~r1_tarski(k3_xboole_0(A_1583, A_1584), A_1584))), inference(superposition, [status(thm), theory('equality')], [c_144218, c_1203])).
% 35.71/26.35  tff(c_145410, plain, (![A_1583, A_1584]: (k7_relat_1(k6_relat_1(A_1583), A_1584)=k6_relat_1(k3_xboole_0(A_1583, A_1584)))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_144915])).
% 35.71/26.35  tff(c_54, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.71/26.35  tff(c_353, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_54])).
% 35.71/26.35  tff(c_380, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_353])).
% 35.71/26.35  tff(c_145618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145410, c_380])).
% 35.71/26.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.71/26.35  
% 35.71/26.35  Inference rules
% 35.71/26.35  ----------------------
% 35.71/26.35  #Ref     : 0
% 35.71/26.35  #Sup     : 35997
% 35.71/26.35  #Fact    : 0
% 35.71/26.35  #Define  : 0
% 35.71/26.35  #Split   : 2
% 35.71/26.35  #Chain   : 0
% 35.71/26.35  #Close   : 0
% 35.71/26.35  
% 35.71/26.35  Ordering : KBO
% 35.71/26.35  
% 35.71/26.35  Simplification rules
% 35.71/26.35  ----------------------
% 35.71/26.35  #Subsume      : 5177
% 35.71/26.35  #Demod        : 33470
% 35.71/26.35  #Tautology    : 9674
% 35.71/26.35  #SimpNegUnit  : 0
% 35.71/26.35  #BackRed      : 189
% 35.71/26.35  
% 35.71/26.35  #Partial instantiations: 0
% 35.71/26.35  #Strategies tried      : 1
% 35.71/26.35  
% 35.71/26.35  Timing (in seconds)
% 35.71/26.35  ----------------------
% 35.71/26.35  Preprocessing        : 0.37
% 35.71/26.35  Parsing              : 0.20
% 35.71/26.35  CNF conversion       : 0.02
% 35.71/26.35  Main loop            : 25.15
% 35.71/26.35  Inferencing          : 2.96
% 35.71/26.35  Reduction            : 12.38
% 35.71/26.35  Demodulation         : 11.13
% 35.71/26.35  BG Simplification    : 0.45
% 35.71/26.35  Subsumption          : 7.90
% 35.71/26.35  Abstraction          : 0.66
% 35.71/26.35  MUC search           : 0.00
% 35.71/26.35  Cooper               : 0.00
% 35.71/26.35  Total                : 25.57
% 35.71/26.35  Index Insertion      : 0.00
% 35.71/26.35  Index Deletion       : 0.00
% 35.71/26.35  Index Matching       : 0.00
% 35.71/26.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
