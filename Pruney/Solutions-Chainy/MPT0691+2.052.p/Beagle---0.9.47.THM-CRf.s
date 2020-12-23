%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 19.90s
% Output     : CNFRefutation 20.03s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 685 expanded)
%              Number of leaves         :   47 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          :  172 (1163 expanded)
%              Number of equality atoms :   71 ( 459 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_80,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_118,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_182,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(A_93,B_94)
      | k4_xboole_0(A_93,B_94) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_193,plain,(
    k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_68])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_204])).

tff(c_130,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_540,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k3_xboole_0(A_126,B_127)) = k4_xboole_0(A_126,B_127) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_552,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k5_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_540])).

tff(c_562,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_552])).

tff(c_44,plain,(
    ! [A_50,B_51] :
      ( v1_relat_1(k7_relat_1(A_50,B_51))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_relat_1(A_70),B_71) = k7_relat_1(B_71,A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ! [A_49] : v1_relat_1(k6_relat_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_96,plain,(
    ! [A_83,B_84] :
      ( k2_xboole_0(A_83,B_84) = B_84
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    k2_xboole_0('#skF_2',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_96])).

tff(c_58,plain,(
    ! [A_67] : k1_relat_1(k6_relat_1(A_67)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_247,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(k10_relat_1(B_102,A_103),k1_relat_1(B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_259,plain,(
    ! [A_67,A_103] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_67),A_103),A_67)
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_247])).

tff(c_297,plain,(
    ! [A_106,A_107] : r1_tarski(k10_relat_1(k6_relat_1(A_106),A_107),A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_259])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_314,plain,(
    ! [A_106,A_107] : k4_xboole_0(k10_relat_1(k6_relat_1(A_106),A_107),A_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_297,c_10])).

tff(c_60,plain,(
    ! [A_67] : k2_relat_1(k6_relat_1(A_67)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_265,plain,(
    ! [A_104] :
      ( k10_relat_1(A_104,k2_relat_1(A_104)) = k1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_277,plain,(
    ! [A_67] :
      ( k10_relat_1(k6_relat_1(A_67),A_67) = k1_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_265])).

tff(c_282,plain,(
    ! [A_67] : k10_relat_1(k6_relat_1(A_67),A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58,c_277])).

tff(c_2605,plain,(
    ! [C_249,A_250,B_251] :
      ( k2_xboole_0(k10_relat_1(C_249,A_250),k10_relat_1(C_249,B_251)) = k10_relat_1(C_249,k2_xboole_0(A_250,B_251))
      | ~ v1_relat_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4289,plain,(
    ! [C_305,A_306,B_307] :
      ( r1_tarski(k10_relat_1(C_305,A_306),k10_relat_1(C_305,k2_xboole_0(A_306,B_307)))
      | ~ v1_relat_1(C_305) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2605,c_26])).

tff(c_4361,plain,(
    ! [A_67,B_307] :
      ( r1_tarski(A_67,k10_relat_1(k6_relat_1(A_67),k2_xboole_0(A_67,B_307)))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_4289])).

tff(c_4393,plain,(
    ! [A_308,B_309] : r1_tarski(A_308,k10_relat_1(k6_relat_1(A_308),k2_xboole_0(A_308,B_309))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4361])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_479,plain,(
    ! [B_121,A_122] :
      ( B_121 = A_122
      | ~ r1_tarski(B_121,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_500,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_479])).

tff(c_4400,plain,(
    ! [A_308,B_309] :
      ( k10_relat_1(k6_relat_1(A_308),k2_xboole_0(A_308,B_309)) = A_308
      | k4_xboole_0(k10_relat_1(k6_relat_1(A_308),k2_xboole_0(A_308,B_309)),A_308) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4393,c_500])).

tff(c_4485,plain,(
    ! [A_310,B_311] : k10_relat_1(k6_relat_1(A_310),k2_xboole_0(A_310,B_311)) = A_310 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_4400])).

tff(c_4663,plain,(
    k10_relat_1(k6_relat_1('#skF_2'),k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4485])).

tff(c_56,plain,(
    ! [A_64,B_66] :
      ( k10_relat_1(A_64,k1_relat_1(B_66)) = k1_relat_1(k5_relat_1(A_64,B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4767,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4663,c_56])).

tff(c_4831,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72,c_4767])).

tff(c_4891,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4831])).

tff(c_4905,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4891])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1668,plain,(
    ! [A_201,B_202] :
      ( k10_relat_1(A_201,k1_relat_1(B_202)) = k1_relat_1(k5_relat_1(A_201,B_202))
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1747,plain,(
    ! [B_202] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_202)),B_202)) = k1_relat_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_202))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_1668])).

tff(c_2040,plain,(
    ! [B_216] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_216)),B_216)) = k1_relat_1(B_216)
      | ~ v1_relat_1(B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1747])).

tff(c_16658,plain,(
    ! [B_461] :
      ( k1_relat_1(k7_relat_1(B_461,k1_relat_1(B_461))) = k1_relat_1(B_461)
      | ~ v1_relat_1(B_461)
      | ~ v1_relat_1(B_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2040])).

tff(c_524,plain,(
    ! [B_124,A_125] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_124,A_125)),A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_536,plain,(
    ! [B_124,A_125] :
      ( k1_relat_1(k7_relat_1(B_124,A_125)) = A_125
      | ~ r1_tarski(A_125,k1_relat_1(k7_relat_1(B_124,A_125)))
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_524,c_2])).

tff(c_16696,plain,(
    ! [B_461] :
      ( k1_relat_1(k7_relat_1(B_461,k1_relat_1(B_461))) = k1_relat_1(B_461)
      | ~ r1_tarski(k1_relat_1(B_461),k1_relat_1(B_461))
      | ~ v1_relat_1(B_461)
      | ~ v1_relat_1(B_461)
      | ~ v1_relat_1(B_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16658,c_536])).

tff(c_16827,plain,(
    ! [B_462] :
      ( k1_relat_1(k7_relat_1(B_462,k1_relat_1(B_462))) = k1_relat_1(B_462)
      | ~ v1_relat_1(B_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16696])).

tff(c_16938,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4905,c_16827])).

tff(c_16988,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_2')) = '#skF_2'
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4905,c_16938])).

tff(c_73270,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_16988])).

tff(c_73329,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_73270])).

tff(c_73333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73329])).

tff(c_73335,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_16988])).

tff(c_46,plain,(
    ! [A_52] :
      ( k9_relat_1(A_52,k1_relat_1(A_52)) = k2_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2102,plain,(
    ! [A_217,C_218,B_219] :
      ( k9_relat_1(k7_relat_1(A_217,C_218),B_219) = k9_relat_1(A_217,B_219)
      | ~ r1_tarski(B_219,C_218)
      | ~ v1_relat_1(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32142,plain,(
    ! [A_634,C_635] :
      ( k9_relat_1(A_634,k1_relat_1(k7_relat_1(A_634,C_635))) = k2_relat_1(k7_relat_1(A_634,C_635))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_634,C_635)),C_635)
      | ~ v1_relat_1(A_634)
      | ~ v1_relat_1(k7_relat_1(A_634,C_635)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2102])).

tff(c_32164,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) = k2_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4905,c_32142])).

tff(c_32187,plain,
    ( k2_relat_1(k7_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6,c_4905,c_32164])).

tff(c_86918,plain,(
    k2_relat_1(k7_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73335,c_32187])).

tff(c_52,plain,(
    ! [A_60] :
      ( k10_relat_1(A_60,k2_relat_1(A_60)) = k1_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86946,plain,
    ( k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2')) = k1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86918,c_52])).

tff(c_86966,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73335,c_4905,c_86946])).

tff(c_1410,plain,(
    ! [A_187,C_188,B_189] :
      ( k3_xboole_0(A_187,k10_relat_1(C_188,B_189)) = k10_relat_1(k7_relat_1(C_188,A_187),B_189)
      | ~ v1_relat_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1416,plain,(
    ! [A_187,C_188,B_189] :
      ( k5_xboole_0(A_187,k10_relat_1(k7_relat_1(C_188,A_187),B_189)) = k4_xboole_0(A_187,k10_relat_1(C_188,B_189))
      | ~ v1_relat_1(C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_12])).

tff(c_87050,plain,
    ( k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k5_xboole_0('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86966,c_1416])).

tff(c_87133,plain,(
    k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_562,c_87050])).

tff(c_87135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_87133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.90/11.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.90/11.81  
% 19.90/11.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.90/11.81  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 19.90/11.81  
% 19.90/11.81  %Foreground sorts:
% 19.90/11.81  
% 19.90/11.81  
% 19.90/11.81  %Background operators:
% 19.90/11.81  
% 19.90/11.81  
% 19.90/11.81  %Foreground operators:
% 19.90/11.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 19.90/11.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.90/11.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.90/11.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.90/11.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.90/11.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.90/11.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.90/11.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.90/11.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.90/11.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.90/11.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.90/11.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.90/11.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.90/11.81  tff('#skF_2', type, '#skF_2': $i).
% 19.90/11.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.90/11.81  tff('#skF_3', type, '#skF_3': $i).
% 19.90/11.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.90/11.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 19.90/11.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.90/11.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.90/11.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.90/11.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.90/11.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.90/11.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.90/11.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.90/11.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 19.90/11.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.90/11.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.90/11.81  
% 20.03/11.83  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 20.03/11.83  tff(f_137, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 20.03/11.83  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.03/11.83  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 20.03/11.83  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 20.03/11.83  tff(f_84, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 20.03/11.83  tff(f_126, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 20.03/11.83  tff(f_80, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 20.03/11.83  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 20.03/11.83  tff(f_118, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 20.03/11.83  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 20.03/11.83  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 20.03/11.83  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 20.03/11.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.03/11.83  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 20.03/11.83  tff(f_122, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 20.03/11.83  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 20.03/11.83  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 20.03/11.83  tff(f_130, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 20.03/11.83  tff(c_182, plain, (![A_93, B_94]: (r1_tarski(A_93, B_94) | k4_xboole_0(A_93, B_94)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.03/11.83  tff(c_68, plain, (~r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 20.03/11.83  tff(c_193, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_68])).
% 20.03/11.83  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 20.03/11.83  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 20.03/11.83  tff(c_204, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.03/11.83  tff(c_218, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_204])).
% 20.03/11.83  tff(c_130, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.03/11.83  tff(c_140, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(resolution, [status(thm)], [c_26, c_130])).
% 20.03/11.83  tff(c_540, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k3_xboole_0(A_126, B_127))=k4_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.03/11.83  tff(c_552, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k5_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_140, c_540])).
% 20.03/11.83  tff(c_562, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_552])).
% 20.03/11.83  tff(c_44, plain, (![A_50, B_51]: (v1_relat_1(k7_relat_1(A_50, B_51)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.03/11.83  tff(c_64, plain, (![A_70, B_71]: (k5_relat_1(k6_relat_1(A_70), B_71)=k7_relat_1(B_71, A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_126])).
% 20.03/11.83  tff(c_42, plain, (![A_49]: (v1_relat_1(k6_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.03/11.83  tff(c_70, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 20.03/11.83  tff(c_96, plain, (![A_83, B_84]: (k2_xboole_0(A_83, B_84)=B_84 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.03/11.83  tff(c_107, plain, (k2_xboole_0('#skF_2', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_96])).
% 20.03/11.83  tff(c_58, plain, (![A_67]: (k1_relat_1(k6_relat_1(A_67))=A_67)), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.03/11.83  tff(c_247, plain, (![B_102, A_103]: (r1_tarski(k10_relat_1(B_102, A_103), k1_relat_1(B_102)) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_99])).
% 20.03/11.83  tff(c_259, plain, (![A_67, A_103]: (r1_tarski(k10_relat_1(k6_relat_1(A_67), A_103), A_67) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_247])).
% 20.03/11.83  tff(c_297, plain, (![A_106, A_107]: (r1_tarski(k10_relat_1(k6_relat_1(A_106), A_107), A_106))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_259])).
% 20.03/11.83  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.03/11.83  tff(c_314, plain, (![A_106, A_107]: (k4_xboole_0(k10_relat_1(k6_relat_1(A_106), A_107), A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_297, c_10])).
% 20.03/11.83  tff(c_60, plain, (![A_67]: (k2_relat_1(k6_relat_1(A_67))=A_67)), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.03/11.83  tff(c_265, plain, (![A_104]: (k10_relat_1(A_104, k2_relat_1(A_104))=k1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_103])).
% 20.03/11.83  tff(c_277, plain, (![A_67]: (k10_relat_1(k6_relat_1(A_67), A_67)=k1_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_265])).
% 20.03/11.83  tff(c_282, plain, (![A_67]: (k10_relat_1(k6_relat_1(A_67), A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_58, c_277])).
% 20.03/11.83  tff(c_2605, plain, (![C_249, A_250, B_251]: (k2_xboole_0(k10_relat_1(C_249, A_250), k10_relat_1(C_249, B_251))=k10_relat_1(C_249, k2_xboole_0(A_250, B_251)) | ~v1_relat_1(C_249))), inference(cnfTransformation, [status(thm)], [f_107])).
% 20.03/11.83  tff(c_4289, plain, (![C_305, A_306, B_307]: (r1_tarski(k10_relat_1(C_305, A_306), k10_relat_1(C_305, k2_xboole_0(A_306, B_307))) | ~v1_relat_1(C_305))), inference(superposition, [status(thm), theory('equality')], [c_2605, c_26])).
% 20.03/11.83  tff(c_4361, plain, (![A_67, B_307]: (r1_tarski(A_67, k10_relat_1(k6_relat_1(A_67), k2_xboole_0(A_67, B_307))) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_4289])).
% 20.03/11.83  tff(c_4393, plain, (![A_308, B_309]: (r1_tarski(A_308, k10_relat_1(k6_relat_1(A_308), k2_xboole_0(A_308, B_309))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4361])).
% 20.03/11.83  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.03/11.83  tff(c_479, plain, (![B_121, A_122]: (B_121=A_122 | ~r1_tarski(B_121, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.03/11.83  tff(c_500, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_479])).
% 20.03/11.83  tff(c_4400, plain, (![A_308, B_309]: (k10_relat_1(k6_relat_1(A_308), k2_xboole_0(A_308, B_309))=A_308 | k4_xboole_0(k10_relat_1(k6_relat_1(A_308), k2_xboole_0(A_308, B_309)), A_308)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4393, c_500])).
% 20.03/11.83  tff(c_4485, plain, (![A_310, B_311]: (k10_relat_1(k6_relat_1(A_310), k2_xboole_0(A_310, B_311))=A_310)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_4400])).
% 20.03/11.83  tff(c_4663, plain, (k10_relat_1(k6_relat_1('#skF_2'), k1_relat_1('#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_107, c_4485])).
% 20.03/11.83  tff(c_56, plain, (![A_64, B_66]: (k10_relat_1(A_64, k1_relat_1(B_66))=k1_relat_1(k5_relat_1(A_64, B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_114])).
% 20.03/11.83  tff(c_4767, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'))='#skF_2' | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4663, c_56])).
% 20.03/11.83  tff(c_4831, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72, c_4767])).
% 20.03/11.83  tff(c_4891, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_4831])).
% 20.03/11.83  tff(c_4905, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4891])).
% 20.03/11.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.03/11.83  tff(c_1668, plain, (![A_201, B_202]: (k10_relat_1(A_201, k1_relat_1(B_202))=k1_relat_1(k5_relat_1(A_201, B_202)) | ~v1_relat_1(B_202) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_114])).
% 20.03/11.83  tff(c_1747, plain, (![B_202]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_202)), B_202))=k1_relat_1(B_202) | ~v1_relat_1(B_202) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_202))))), inference(superposition, [status(thm), theory('equality')], [c_282, c_1668])).
% 20.03/11.83  tff(c_2040, plain, (![B_216]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_216)), B_216))=k1_relat_1(B_216) | ~v1_relat_1(B_216))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1747])).
% 20.03/11.83  tff(c_16658, plain, (![B_461]: (k1_relat_1(k7_relat_1(B_461, k1_relat_1(B_461)))=k1_relat_1(B_461) | ~v1_relat_1(B_461) | ~v1_relat_1(B_461))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2040])).
% 20.03/11.83  tff(c_524, plain, (![B_124, A_125]: (r1_tarski(k1_relat_1(k7_relat_1(B_124, A_125)), A_125) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.03/11.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.03/11.83  tff(c_536, plain, (![B_124, A_125]: (k1_relat_1(k7_relat_1(B_124, A_125))=A_125 | ~r1_tarski(A_125, k1_relat_1(k7_relat_1(B_124, A_125))) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_524, c_2])).
% 20.03/11.83  tff(c_16696, plain, (![B_461]: (k1_relat_1(k7_relat_1(B_461, k1_relat_1(B_461)))=k1_relat_1(B_461) | ~r1_tarski(k1_relat_1(B_461), k1_relat_1(B_461)) | ~v1_relat_1(B_461) | ~v1_relat_1(B_461) | ~v1_relat_1(B_461))), inference(superposition, [status(thm), theory('equality')], [c_16658, c_536])).
% 20.03/11.83  tff(c_16827, plain, (![B_462]: (k1_relat_1(k7_relat_1(B_462, k1_relat_1(B_462)))=k1_relat_1(B_462) | ~v1_relat_1(B_462))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16696])).
% 20.03/11.83  tff(c_16938, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4905, c_16827])).
% 20.03/11.83  tff(c_16988, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_2'))='#skF_2' | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4905, c_16938])).
% 20.03/11.83  tff(c_73270, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_16988])).
% 20.03/11.83  tff(c_73329, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_73270])).
% 20.03/11.83  tff(c_73333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_73329])).
% 20.03/11.83  tff(c_73335, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_16988])).
% 20.03/11.83  tff(c_46, plain, (![A_52]: (k9_relat_1(A_52, k1_relat_1(A_52))=k2_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_88])).
% 20.03/11.83  tff(c_2102, plain, (![A_217, C_218, B_219]: (k9_relat_1(k7_relat_1(A_217, C_218), B_219)=k9_relat_1(A_217, B_219) | ~r1_tarski(B_219, C_218) | ~v1_relat_1(A_217))), inference(cnfTransformation, [status(thm)], [f_95])).
% 20.03/11.83  tff(c_32142, plain, (![A_634, C_635]: (k9_relat_1(A_634, k1_relat_1(k7_relat_1(A_634, C_635)))=k2_relat_1(k7_relat_1(A_634, C_635)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_634, C_635)), C_635) | ~v1_relat_1(A_634) | ~v1_relat_1(k7_relat_1(A_634, C_635)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2102])).
% 20.03/11.83  tff(c_32164, plain, (k9_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))=k2_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4905, c_32142])).
% 20.03/11.83  tff(c_32187, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6, c_4905, c_32164])).
% 20.03/11.83  tff(c_86918, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73335, c_32187])).
% 20.03/11.83  tff(c_52, plain, (![A_60]: (k10_relat_1(A_60, k2_relat_1(A_60))=k1_relat_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_103])).
% 20.03/11.83  tff(c_86946, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_86918, c_52])).
% 20.03/11.83  tff(c_86966, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73335, c_4905, c_86946])).
% 20.03/11.83  tff(c_1410, plain, (![A_187, C_188, B_189]: (k3_xboole_0(A_187, k10_relat_1(C_188, B_189))=k10_relat_1(k7_relat_1(C_188, A_187), B_189) | ~v1_relat_1(C_188))), inference(cnfTransformation, [status(thm)], [f_130])).
% 20.03/11.83  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.03/11.83  tff(c_1416, plain, (![A_187, C_188, B_189]: (k5_xboole_0(A_187, k10_relat_1(k7_relat_1(C_188, A_187), B_189))=k4_xboole_0(A_187, k10_relat_1(C_188, B_189)) | ~v1_relat_1(C_188))), inference(superposition, [status(thm), theory('equality')], [c_1410, c_12])).
% 20.03/11.83  tff(c_87050, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k5_xboole_0('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86966, c_1416])).
% 20.03/11.83  tff(c_87133, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_562, c_87050])).
% 20.03/11.83  tff(c_87135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_87133])).
% 20.03/11.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.03/11.83  
% 20.03/11.83  Inference rules
% 20.03/11.83  ----------------------
% 20.03/11.83  #Ref     : 0
% 20.03/11.83  #Sup     : 20656
% 20.03/11.83  #Fact    : 0
% 20.03/11.83  #Define  : 0
% 20.03/11.83  #Split   : 3
% 20.03/11.83  #Chain   : 0
% 20.03/11.83  #Close   : 0
% 20.03/11.83  
% 20.03/11.83  Ordering : KBO
% 20.03/11.83  
% 20.03/11.83  Simplification rules
% 20.03/11.83  ----------------------
% 20.03/11.83  #Subsume      : 4000
% 20.03/11.83  #Demod        : 17995
% 20.03/11.83  #Tautology    : 9946
% 20.03/11.83  #SimpNegUnit  : 1
% 20.03/11.83  #BackRed      : 1
% 20.03/11.83  
% 20.03/11.83  #Partial instantiations: 0
% 20.03/11.83  #Strategies tried      : 1
% 20.03/11.83  
% 20.03/11.83  Timing (in seconds)
% 20.03/11.83  ----------------------
% 20.03/11.84  Preprocessing        : 0.35
% 20.03/11.84  Parsing              : 0.18
% 20.03/11.84  CNF conversion       : 0.02
% 20.03/11.84  Main loop            : 10.68
% 20.03/11.84  Inferencing          : 1.70
% 20.03/11.84  Reduction            : 5.52
% 20.03/11.84  Demodulation         : 4.81
% 20.03/11.84  BG Simplification    : 0.20
% 20.03/11.84  Subsumption          : 2.78
% 20.03/11.84  Abstraction          : 0.33
% 20.03/11.84  MUC search           : 0.00
% 20.03/11.84  Cooper               : 0.00
% 20.03/11.84  Total                : 11.07
% 20.03/11.84  Index Insertion      : 0.00
% 20.03/11.84  Index Deletion       : 0.00
% 20.03/11.84  Index Matching       : 0.00
% 20.03/11.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
