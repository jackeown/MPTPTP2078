%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 9.54s
% Output     : CNFRefutation 9.72s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 174 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 252 expanded)
%              Number of equality atoms :   47 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_76,B_77] : k1_setfam_1(k2_tarski(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_136,plain,(
    ! [B_78,A_79] : k1_setfam_1(k2_tarski(B_78,A_79)) = k3_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_26,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,(
    ! [B_80,A_81] : k3_xboole_0(B_80,A_81) = k3_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_26])).

tff(c_174,plain,(
    ! [B_80,A_81] : r1_tarski(k3_xboole_0(B_80,A_81),A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_8])).

tff(c_30,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [B_42,A_41] :
      ( k5_relat_1(B_42,k6_relat_1(A_41)) = k8_relat_1(A_41,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_378,plain,(
    ! [A_106,B_107] :
      ( k5_relat_1(k6_relat_1(A_106),B_107) = k7_relat_1(B_107,A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_413,plain,(
    ! [A_41,A_106] :
      ( k8_relat_1(A_41,k6_relat_1(A_106)) = k7_relat_1(k6_relat_1(A_41),A_106)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_378])).

tff(c_436,plain,(
    ! [A_41,A_106] : k8_relat_1(A_41,k6_relat_1(A_106)) = k7_relat_1(k6_relat_1(A_41),A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_413])).

tff(c_40,plain,(
    ! [A_54] : k2_relat_1(k6_relat_1(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_582,plain,(
    ! [B_124,A_125] :
      ( k5_relat_1(B_124,k6_relat_1(A_125)) = B_124
      | ~ r1_tarski(k2_relat_1(B_124),A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_585,plain,(
    ! [A_54,A_125] :
      ( k5_relat_1(k6_relat_1(A_54),k6_relat_1(A_125)) = k6_relat_1(A_54)
      | ~ r1_tarski(A_54,A_125)
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_582])).

tff(c_2397,plain,(
    ! [A_206,A_207] :
      ( k5_relat_1(k6_relat_1(A_206),k6_relat_1(A_207)) = k6_relat_1(A_206)
      | ~ r1_tarski(A_206,A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_585])).

tff(c_2419,plain,(
    ! [A_207,A_206] :
      ( k8_relat_1(A_207,k6_relat_1(A_206)) = k6_relat_1(A_206)
      | ~ v1_relat_1(k6_relat_1(A_206))
      | ~ r1_tarski(A_206,A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2397,c_32])).

tff(c_2475,plain,(
    ! [A_207,A_206] :
      ( k7_relat_1(k6_relat_1(A_207),A_206) = k6_relat_1(A_206)
      | ~ r1_tarski(A_206,A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_436,c_2419])).

tff(c_503,plain,(
    ! [A_115,A_116] : k8_relat_1(A_115,k6_relat_1(A_116)) = k7_relat_1(k6_relat_1(A_115),A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_413])).

tff(c_299,plain,(
    ! [B_96,A_97] :
      ( k5_relat_1(B_96,k6_relat_1(A_97)) = k8_relat_1(A_97,B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k5_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_320,plain,(
    ! [A_97,B_96] :
      ( v1_relat_1(k8_relat_1(A_97,B_96))
      | ~ v1_relat_1(k6_relat_1(A_97))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_28])).

tff(c_339,plain,(
    ! [A_97,B_96] :
      ( v1_relat_1(k8_relat_1(A_97,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_320])).

tff(c_513,plain,(
    ! [A_115,A_116] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_115),A_116))
      | ~ v1_relat_1(k6_relat_1(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_339])).

tff(c_523,plain,(
    ! [A_115,A_116] : v1_relat_1(k7_relat_1(k6_relat_1(A_115),A_116)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_513])).

tff(c_38,plain,(
    ! [A_54] : k1_relat_1(k6_relat_1(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_459,plain,(
    ! [B_111,A_112] :
      ( k3_xboole_0(k1_relat_1(B_111),A_112) = k1_relat_1(k7_relat_1(B_111,A_112))
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_488,plain,(
    ! [A_54,A_112] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_54),A_112)) = k3_xboole_0(A_54,A_112)
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_459])).

tff(c_492,plain,(
    ! [A_54,A_112] : k1_relat_1(k7_relat_1(k6_relat_1(A_54),A_112)) = k3_xboole_0(A_54,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_488])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_762,plain,(
    ! [A_142,B_143] :
      ( k5_relat_1(k6_relat_1(A_142),B_143) = B_143
      | ~ r1_tarski(k1_relat_1(B_143),A_142)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_788,plain,(
    ! [B_143] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_143)),B_143) = B_143
      | ~ v1_relat_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_6,c_762])).

tff(c_964,plain,(
    ! [A_157,B_158,C_159] :
      ( k8_relat_1(A_157,k5_relat_1(B_158,C_159)) = k5_relat_1(B_158,k8_relat_1(A_157,C_159))
      | ~ v1_relat_1(C_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_993,plain,(
    ! [B_42,A_157,A_41] :
      ( k5_relat_1(B_42,k8_relat_1(A_157,k6_relat_1(A_41))) = k8_relat_1(A_157,k8_relat_1(A_41,B_42))
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_964])).

tff(c_4314,plain,(
    ! [B_244,A_245,A_246] :
      ( k5_relat_1(B_244,k7_relat_1(k6_relat_1(A_245),A_246)) = k8_relat_1(A_245,k8_relat_1(A_246,B_244))
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_436,c_993])).

tff(c_4380,plain,(
    ! [A_245,A_246] :
      ( k8_relat_1(A_245,k8_relat_1(A_246,k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246))))) = k7_relat_1(k6_relat_1(A_245),A_246)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_4314])).

tff(c_15184,plain,(
    ! [A_385,A_386] : k8_relat_1(A_385,k7_relat_1(k6_relat_1(A_386),k3_xboole_0(A_385,A_386))) = k7_relat_1(k6_relat_1(A_385),A_386) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_30,c_492,c_436,c_4380])).

tff(c_15293,plain,(
    ! [A_385,A_207] :
      ( k8_relat_1(A_385,k6_relat_1(k3_xboole_0(A_385,A_207))) = k7_relat_1(k6_relat_1(A_385),A_207)
      | ~ r1_tarski(k3_xboole_0(A_385,A_207),A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2475,c_15184])).

tff(c_15378,plain,(
    ! [A_387,A_388] : k7_relat_1(k6_relat_1(A_387),k3_xboole_0(A_387,A_388)) = k7_relat_1(k6_relat_1(A_387),A_388) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_436,c_15293])).

tff(c_15438,plain,(
    ! [A_387,A_388] :
      ( k7_relat_1(k6_relat_1(A_387),A_388) = k6_relat_1(k3_xboole_0(A_387,A_388))
      | ~ r1_tarski(k3_xboole_0(A_387,A_388),A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15378,c_2475])).

tff(c_15611,plain,(
    ! [A_387,A_388] : k7_relat_1(k6_relat_1(A_387),A_388) = k6_relat_1(k3_xboole_0(A_387,A_388)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15438])).

tff(c_56,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_406,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_56])).

tff(c_433,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_406])).

tff(c_15666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15611,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.54/3.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.54/3.56  
% 9.54/3.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.54/3.56  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.54/3.56  
% 9.54/3.56  %Foreground sorts:
% 9.54/3.56  
% 9.54/3.56  
% 9.54/3.56  %Background operators:
% 9.54/3.56  
% 9.54/3.56  
% 9.54/3.56  %Foreground operators:
% 9.54/3.56  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.54/3.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.54/3.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.54/3.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.54/3.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.54/3.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.54/3.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.54/3.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.54/3.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.54/3.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.54/3.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.54/3.56  tff('#skF_2', type, '#skF_2': $i).
% 9.54/3.56  tff('#skF_1', type, '#skF_1': $i).
% 9.54/3.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.54/3.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.54/3.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.54/3.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.54/3.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.54/3.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.54/3.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.54/3.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.54/3.56  
% 9.72/3.58  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.72/3.58  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.72/3.58  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.72/3.58  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.72/3.58  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 9.72/3.58  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 9.72/3.58  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.72/3.58  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 9.72/3.58  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.72/3.58  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 9.72/3.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.72/3.58  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 9.72/3.58  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 9.72/3.58  tff(f_117, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 9.72/3.58  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.72/3.58  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.72/3.58  tff(c_121, plain, (![A_76, B_77]: (k1_setfam_1(k2_tarski(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.72/3.58  tff(c_136, plain, (![B_78, A_79]: (k1_setfam_1(k2_tarski(B_78, A_79))=k3_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 9.72/3.58  tff(c_26, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.72/3.58  tff(c_159, plain, (![B_80, A_81]: (k3_xboole_0(B_80, A_81)=k3_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_136, c_26])).
% 9.72/3.58  tff(c_174, plain, (![B_80, A_81]: (r1_tarski(k3_xboole_0(B_80, A_81), A_81))), inference(superposition, [status(thm), theory('equality')], [c_159, c_8])).
% 9.72/3.58  tff(c_30, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.72/3.58  tff(c_32, plain, (![B_42, A_41]: (k5_relat_1(B_42, k6_relat_1(A_41))=k8_relat_1(A_41, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.72/3.58  tff(c_378, plain, (![A_106, B_107]: (k5_relat_1(k6_relat_1(A_106), B_107)=k7_relat_1(B_107, A_106) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.72/3.58  tff(c_413, plain, (![A_41, A_106]: (k8_relat_1(A_41, k6_relat_1(A_106))=k7_relat_1(k6_relat_1(A_41), A_106) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_106)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_378])).
% 9.72/3.58  tff(c_436, plain, (![A_41, A_106]: (k8_relat_1(A_41, k6_relat_1(A_106))=k7_relat_1(k6_relat_1(A_41), A_106))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_413])).
% 9.72/3.58  tff(c_40, plain, (![A_54]: (k2_relat_1(k6_relat_1(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.72/3.58  tff(c_582, plain, (![B_124, A_125]: (k5_relat_1(B_124, k6_relat_1(A_125))=B_124 | ~r1_tarski(k2_relat_1(B_124), A_125) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.72/3.58  tff(c_585, plain, (![A_54, A_125]: (k5_relat_1(k6_relat_1(A_54), k6_relat_1(A_125))=k6_relat_1(A_54) | ~r1_tarski(A_54, A_125) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_582])).
% 9.72/3.58  tff(c_2397, plain, (![A_206, A_207]: (k5_relat_1(k6_relat_1(A_206), k6_relat_1(A_207))=k6_relat_1(A_206) | ~r1_tarski(A_206, A_207))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_585])).
% 9.72/3.58  tff(c_2419, plain, (![A_207, A_206]: (k8_relat_1(A_207, k6_relat_1(A_206))=k6_relat_1(A_206) | ~v1_relat_1(k6_relat_1(A_206)) | ~r1_tarski(A_206, A_207))), inference(superposition, [status(thm), theory('equality')], [c_2397, c_32])).
% 9.72/3.58  tff(c_2475, plain, (![A_207, A_206]: (k7_relat_1(k6_relat_1(A_207), A_206)=k6_relat_1(A_206) | ~r1_tarski(A_206, A_207))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_436, c_2419])).
% 9.72/3.58  tff(c_503, plain, (![A_115, A_116]: (k8_relat_1(A_115, k6_relat_1(A_116))=k7_relat_1(k6_relat_1(A_115), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_413])).
% 9.72/3.58  tff(c_299, plain, (![B_96, A_97]: (k5_relat_1(B_96, k6_relat_1(A_97))=k8_relat_1(A_97, B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.72/3.58  tff(c_28, plain, (![A_38, B_39]: (v1_relat_1(k5_relat_1(A_38, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.72/3.58  tff(c_320, plain, (![A_97, B_96]: (v1_relat_1(k8_relat_1(A_97, B_96)) | ~v1_relat_1(k6_relat_1(A_97)) | ~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_299, c_28])).
% 9.72/3.58  tff(c_339, plain, (![A_97, B_96]: (v1_relat_1(k8_relat_1(A_97, B_96)) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_320])).
% 9.72/3.58  tff(c_513, plain, (![A_115, A_116]: (v1_relat_1(k7_relat_1(k6_relat_1(A_115), A_116)) | ~v1_relat_1(k6_relat_1(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_503, c_339])).
% 9.72/3.58  tff(c_523, plain, (![A_115, A_116]: (v1_relat_1(k7_relat_1(k6_relat_1(A_115), A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_513])).
% 9.72/3.58  tff(c_38, plain, (![A_54]: (k1_relat_1(k6_relat_1(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.72/3.58  tff(c_459, plain, (![B_111, A_112]: (k3_xboole_0(k1_relat_1(B_111), A_112)=k1_relat_1(k7_relat_1(B_111, A_112)) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.72/3.58  tff(c_488, plain, (![A_54, A_112]: (k1_relat_1(k7_relat_1(k6_relat_1(A_54), A_112))=k3_xboole_0(A_54, A_112) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_459])).
% 9.72/3.58  tff(c_492, plain, (![A_54, A_112]: (k1_relat_1(k7_relat_1(k6_relat_1(A_54), A_112))=k3_xboole_0(A_54, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_488])).
% 9.72/3.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.72/3.58  tff(c_762, plain, (![A_142, B_143]: (k5_relat_1(k6_relat_1(A_142), B_143)=B_143 | ~r1_tarski(k1_relat_1(B_143), A_142) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.72/3.58  tff(c_788, plain, (![B_143]: (k5_relat_1(k6_relat_1(k1_relat_1(B_143)), B_143)=B_143 | ~v1_relat_1(B_143))), inference(resolution, [status(thm)], [c_6, c_762])).
% 9.72/3.58  tff(c_964, plain, (![A_157, B_158, C_159]: (k8_relat_1(A_157, k5_relat_1(B_158, C_159))=k5_relat_1(B_158, k8_relat_1(A_157, C_159)) | ~v1_relat_1(C_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.72/3.58  tff(c_993, plain, (![B_42, A_157, A_41]: (k5_relat_1(B_42, k8_relat_1(A_157, k6_relat_1(A_41)))=k8_relat_1(A_157, k8_relat_1(A_41, B_42)) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(B_42) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_32, c_964])).
% 9.72/3.58  tff(c_4314, plain, (![B_244, A_245, A_246]: (k5_relat_1(B_244, k7_relat_1(k6_relat_1(A_245), A_246))=k8_relat_1(A_245, k8_relat_1(A_246, B_244)) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_436, c_993])).
% 9.72/3.58  tff(c_4380, plain, (![A_245, A_246]: (k8_relat_1(A_245, k8_relat_1(A_246, k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))))=k7_relat_1(k6_relat_1(A_245), A_246) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))), inference(superposition, [status(thm), theory('equality')], [c_788, c_4314])).
% 9.72/3.58  tff(c_15184, plain, (![A_385, A_386]: (k8_relat_1(A_385, k7_relat_1(k6_relat_1(A_386), k3_xboole_0(A_385, A_386)))=k7_relat_1(k6_relat_1(A_385), A_386))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_30, c_492, c_436, c_4380])).
% 9.72/3.58  tff(c_15293, plain, (![A_385, A_207]: (k8_relat_1(A_385, k6_relat_1(k3_xboole_0(A_385, A_207)))=k7_relat_1(k6_relat_1(A_385), A_207) | ~r1_tarski(k3_xboole_0(A_385, A_207), A_207))), inference(superposition, [status(thm), theory('equality')], [c_2475, c_15184])).
% 9.72/3.58  tff(c_15378, plain, (![A_387, A_388]: (k7_relat_1(k6_relat_1(A_387), k3_xboole_0(A_387, A_388))=k7_relat_1(k6_relat_1(A_387), A_388))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_436, c_15293])).
% 9.72/3.58  tff(c_15438, plain, (![A_387, A_388]: (k7_relat_1(k6_relat_1(A_387), A_388)=k6_relat_1(k3_xboole_0(A_387, A_388)) | ~r1_tarski(k3_xboole_0(A_387, A_388), A_387))), inference(superposition, [status(thm), theory('equality')], [c_15378, c_2475])).
% 9.72/3.58  tff(c_15611, plain, (![A_387, A_388]: (k7_relat_1(k6_relat_1(A_387), A_388)=k6_relat_1(k3_xboole_0(A_387, A_388)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15438])).
% 9.72/3.58  tff(c_56, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.72/3.58  tff(c_406, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_56])).
% 9.72/3.58  tff(c_433, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_406])).
% 9.72/3.58  tff(c_15666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15611, c_433])).
% 9.72/3.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.72/3.58  
% 9.72/3.58  Inference rules
% 9.72/3.58  ----------------------
% 9.72/3.58  #Ref     : 0
% 9.72/3.58  #Sup     : 3912
% 9.72/3.58  #Fact    : 0
% 9.72/3.58  #Define  : 0
% 9.72/3.58  #Split   : 2
% 9.72/3.58  #Chain   : 0
% 9.72/3.58  #Close   : 0
% 9.72/3.58  
% 9.72/3.58  Ordering : KBO
% 9.72/3.58  
% 9.72/3.58  Simplification rules
% 9.72/3.58  ----------------------
% 9.72/3.58  #Subsume      : 572
% 9.72/3.58  #Demod        : 3700
% 9.72/3.58  #Tautology    : 1450
% 9.72/3.58  #SimpNegUnit  : 0
% 9.72/3.58  #BackRed      : 20
% 9.72/3.58  
% 9.72/3.58  #Partial instantiations: 0
% 9.72/3.58  #Strategies tried      : 1
% 9.72/3.58  
% 9.72/3.58  Timing (in seconds)
% 9.72/3.58  ----------------------
% 9.72/3.58  Preprocessing        : 0.36
% 9.72/3.58  Parsing              : 0.19
% 9.72/3.58  CNF conversion       : 0.02
% 9.72/3.58  Main loop            : 2.44
% 9.72/3.58  Inferencing          : 0.61
% 9.72/3.58  Reduction            : 1.18
% 9.72/3.58  Demodulation         : 1.01
% 9.72/3.58  BG Simplification    : 0.09
% 9.72/3.58  Subsumption          : 0.43
% 9.72/3.58  Abstraction          : 0.14
% 9.72/3.58  MUC search           : 0.00
% 9.72/3.58  Cooper               : 0.00
% 9.72/3.58  Total                : 2.83
% 9.72/3.58  Index Insertion      : 0.00
% 9.72/3.58  Index Deletion       : 0.00
% 9.72/3.58  Index Matching       : 0.00
% 9.72/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
