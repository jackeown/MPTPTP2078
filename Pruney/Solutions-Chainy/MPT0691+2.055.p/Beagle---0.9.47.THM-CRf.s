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
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  119 (1219 expanded)
%              Number of leaves         :   38 ( 443 expanded)
%              Depth                    :   27
%              Number of atoms          :  174 (2185 expanded)
%              Number of equality atoms :   78 (1003 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_85,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_48])).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_181,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_193,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_190])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k7_relat_1(A_25,B_26))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_33] : k1_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_42,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_242,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_262,plain,(
    ! [B_77] :
      ( k7_relat_1(B_77,k1_relat_1(B_77)) = B_77
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_242])).

tff(c_280,plain,(
    ! [A_33] :
      ( k7_relat_1(k6_relat_1(A_33),A_33) = k6_relat_1(A_33)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_262])).

tff(c_285,plain,(
    ! [A_33] : k7_relat_1(k6_relat_1(A_33),A_33) = k6_relat_1(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_280])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_570,plain,(
    ! [B_107,B_108] :
      ( k7_relat_1(B_107,B_108) = B_107
      | ~ v1_relat_1(B_107)
      | k4_xboole_0(k1_relat_1(B_107),B_108) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_242])).

tff(c_580,plain,(
    ! [A_33,B_108] :
      ( k7_relat_1(k6_relat_1(A_33),B_108) = k6_relat_1(A_33)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | k4_xboole_0(A_33,B_108) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_570])).

tff(c_584,plain,(
    ! [A_33,B_108] :
      ( k7_relat_1(k6_relat_1(A_33),B_108) = k6_relat_1(A_33)
      | k4_xboole_0(A_33,B_108) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_580])).

tff(c_36,plain,(
    ! [A_33] : k2_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [A_63] :
      ( k10_relat_1(A_63,k2_relat_1(A_63)) = k1_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_167,plain,(
    ! [A_33] :
      ( k10_relat_1(k6_relat_1(A_33),A_33) = k1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_158])).

tff(c_171,plain,(
    ! [A_33] : k10_relat_1(k6_relat_1(A_33),A_33) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_167])).

tff(c_252,plain,(
    ! [A_33,A_76] :
      ( k7_relat_1(k6_relat_1(A_33),A_76) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_76)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_242])).

tff(c_260,plain,(
    ! [A_33,A_76] :
      ( k7_relat_1(k6_relat_1(A_33),A_76) = k6_relat_1(A_33)
      | ~ r1_tarski(A_33,A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_252])).

tff(c_463,plain,(
    ! [A_93,C_94,B_95] :
      ( k3_xboole_0(A_93,k10_relat_1(C_94,B_95)) = k10_relat_1(k7_relat_1(C_94,A_93),B_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_479,plain,(
    ! [A_33,A_93] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_33),A_93),A_33) = k3_xboole_0(A_93,A_33)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_463])).

tff(c_491,plain,(
    ! [A_96,A_97] : k10_relat_1(k7_relat_1(k6_relat_1(A_96),A_97),A_96) = k3_xboole_0(A_97,A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_479])).

tff(c_503,plain,(
    ! [A_76,A_33] :
      ( k3_xboole_0(A_76,A_33) = k10_relat_1(k6_relat_1(A_33),A_33)
      | ~ r1_tarski(A_33,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_491])).

tff(c_517,plain,(
    ! [A_98,A_99] :
      ( k3_xboole_0(A_98,A_99) = A_99
      | ~ r1_tarski(A_99,A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_503])).

tff(c_532,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_50,c_517])).

tff(c_38,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_35,A_34)),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_877,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,k1_relat_1(k7_relat_1(B_120,A_119))) = k1_relat_1(k7_relat_1(B_120,A_119))
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_38,c_517])).

tff(c_895,plain,(
    ! [A_76,A_33] :
      ( k3_xboole_0(A_76,k1_relat_1(k6_relat_1(A_33))) = k1_relat_1(k7_relat_1(k6_relat_1(A_33),A_76))
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ r1_tarski(A_33,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_877])).

tff(c_911,plain,(
    ! [A_121,A_122] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_121),A_122)) = k3_xboole_0(A_122,A_121)
      | ~ r1_tarski(A_121,A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_895])).

tff(c_530,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,k1_relat_1(k7_relat_1(B_35,A_34))) = k1_relat_1(k7_relat_1(B_35,A_34))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_38,c_517])).

tff(c_917,plain,(
    ! [A_122,A_121] :
      ( k3_xboole_0(A_122,k3_xboole_0(A_122,A_121)) = k1_relat_1(k7_relat_1(k6_relat_1(A_121),A_122))
      | ~ v1_relat_1(k6_relat_1(A_121))
      | ~ r1_tarski(A_121,A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_530])).

tff(c_2196,plain,(
    ! [A_165,A_166] :
      ( k3_xboole_0(A_165,k3_xboole_0(A_165,A_166)) = k1_relat_1(k7_relat_1(k6_relat_1(A_166),A_165))
      | ~ r1_tarski(A_166,A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_917])).

tff(c_2346,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_2196])).

tff(c_2375,plain,(
    k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_532,c_2346])).

tff(c_261,plain,(
    ! [B_75] :
      ( k7_relat_1(B_75,k1_relat_1(B_75)) = B_75
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_242])).

tff(c_2423,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),'#skF_1') = k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2375,c_261])).

tff(c_2717,plain,(
    ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2423])).

tff(c_2720,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_1'))
    | k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_2717])).

tff(c_2729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_42,c_2720])).

tff(c_2730,plain,(
    k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),'#skF_1') = k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2423])).

tff(c_2899,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k7_relat_1(k6_relat_1('#skF_1'),'#skF_1')
    | k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_2730])).

tff(c_2926,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_285,c_2899])).

tff(c_695,plain,(
    ! [A_113,B_114] :
      ( k7_relat_1(A_113,k1_relat_1(k7_relat_1(B_114,k1_relat_1(A_113)))) = k7_relat_1(A_113,k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_757,plain,(
    ! [A_33,B_114] :
      ( k7_relat_1(k6_relat_1(A_33),k1_relat_1(k7_relat_1(B_114,A_33))) = k7_relat_1(k6_relat_1(A_33),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_695])).

tff(c_2929,plain,(
    ! [A_177,B_178] :
      ( k7_relat_1(k6_relat_1(A_177),k1_relat_1(k7_relat_1(B_178,A_177))) = k7_relat_1(k6_relat_1(A_177),k1_relat_1(B_178))
      | ~ v1_relat_1(B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_757])).

tff(c_2986,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_177),k1_relat_1(B_178))),k1_relat_1(k7_relat_1(B_178,A_177)))
      | ~ v1_relat_1(k6_relat_1(A_177))
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2929,c_38])).

tff(c_3707,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_191),k1_relat_1(B_192))),k1_relat_1(k7_relat_1(B_192,A_191)))
      | ~ v1_relat_1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2986])).

tff(c_3729,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_3707])).

tff(c_3847,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34,c_3729])).

tff(c_150,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_61,A_62)),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(k7_relat_1(B_61,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(k7_relat_1(B_61,A_62)))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_3895,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3847,c_156])).

tff(c_3912,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3895])).

tff(c_28,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(k7_relat_1(B_28,A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5182,plain,(
    ! [A_201,B_202] :
      ( k9_relat_1(A_201,k1_relat_1(k7_relat_1(B_202,k1_relat_1(A_201)))) = k2_relat_1(k7_relat_1(A_201,k1_relat_1(B_202)))
      | ~ v1_relat_1(A_201)
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_28])).

tff(c_5215,plain,
    ( k2_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))) = k9_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_5182])).

tff(c_5300,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42,c_52,c_34,c_34,c_5215])).

tff(c_30,plain,(
    ! [A_29] :
      ( k10_relat_1(A_29,k2_relat_1(A_29)) = k1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5342,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5300,c_30])).

tff(c_5352,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3912,c_5342])).

tff(c_12417,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5352])).

tff(c_12420,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_12417])).

tff(c_12424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12420])).

tff(c_12425,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5352])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_469,plain,(
    ! [A_93,C_94,B_95] :
      ( k5_xboole_0(A_93,k10_relat_1(k7_relat_1(C_94,A_93),B_95)) = k4_xboole_0(A_93,k10_relat_1(C_94,B_95))
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_14])).

tff(c_12433,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12425,c_469])).

tff(c_12448,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_193,c_12433])).

tff(c_12450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_12448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.67  
% 7.62/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.67  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.62/2.67  
% 7.62/2.67  %Foreground sorts:
% 7.62/2.67  
% 7.62/2.67  
% 7.62/2.67  %Background operators:
% 7.62/2.67  
% 7.62/2.67  
% 7.62/2.67  %Foreground operators:
% 7.62/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.62/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/2.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.62/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/2.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/2.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.62/2.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.62/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/2.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.62/2.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.62/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.62/2.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.62/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.62/2.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.62/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.62/2.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.62/2.67  
% 7.62/2.69  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.62/2.69  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 7.62/2.69  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.62/2.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.62/2.69  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.62/2.69  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.62/2.69  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.62/2.69  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.62/2.69  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.62/2.69  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.62/2.69  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 7.62/2.69  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 7.62/2.69  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 7.62/2.69  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.62/2.69  tff(c_85, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | k4_xboole_0(A_50, B_51)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.62/2.69  tff(c_48, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.62/2.69  tff(c_89, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_48])).
% 7.62/2.69  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.62/2.69  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.62/2.69  tff(c_108, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.62/2.69  tff(c_120, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_108])).
% 7.62/2.69  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.62/2.69  tff(c_181, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.62/2.69  tff(c_190, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 7.62/2.69  tff(c_193, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_190])).
% 7.62/2.69  tff(c_26, plain, (![A_25, B_26]: (v1_relat_1(k7_relat_1(A_25, B_26)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.62/2.69  tff(c_34, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.62/2.69  tff(c_50, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.62/2.69  tff(c_119, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_108])).
% 7.62/2.69  tff(c_42, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.62/2.69  tff(c_242, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~r1_tarski(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.62/2.69  tff(c_262, plain, (![B_77]: (k7_relat_1(B_77, k1_relat_1(B_77))=B_77 | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_8, c_242])).
% 7.62/2.69  tff(c_280, plain, (![A_33]: (k7_relat_1(k6_relat_1(A_33), A_33)=k6_relat_1(A_33) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_262])).
% 7.62/2.69  tff(c_285, plain, (![A_33]: (k7_relat_1(k6_relat_1(A_33), A_33)=k6_relat_1(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_280])).
% 7.62/2.69  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.62/2.69  tff(c_570, plain, (![B_107, B_108]: (k7_relat_1(B_107, B_108)=B_107 | ~v1_relat_1(B_107) | k4_xboole_0(k1_relat_1(B_107), B_108)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_242])).
% 7.62/2.69  tff(c_580, plain, (![A_33, B_108]: (k7_relat_1(k6_relat_1(A_33), B_108)=k6_relat_1(A_33) | ~v1_relat_1(k6_relat_1(A_33)) | k4_xboole_0(A_33, B_108)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_570])).
% 7.62/2.69  tff(c_584, plain, (![A_33, B_108]: (k7_relat_1(k6_relat_1(A_33), B_108)=k6_relat_1(A_33) | k4_xboole_0(A_33, B_108)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_580])).
% 7.62/2.69  tff(c_36, plain, (![A_33]: (k2_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.62/2.69  tff(c_158, plain, (![A_63]: (k10_relat_1(A_63, k2_relat_1(A_63))=k1_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.62/2.69  tff(c_167, plain, (![A_33]: (k10_relat_1(k6_relat_1(A_33), A_33)=k1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_158])).
% 7.62/2.69  tff(c_171, plain, (![A_33]: (k10_relat_1(k6_relat_1(A_33), A_33)=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_167])).
% 7.62/2.69  tff(c_252, plain, (![A_33, A_76]: (k7_relat_1(k6_relat_1(A_33), A_76)=k6_relat_1(A_33) | ~r1_tarski(A_33, A_76) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_242])).
% 7.62/2.69  tff(c_260, plain, (![A_33, A_76]: (k7_relat_1(k6_relat_1(A_33), A_76)=k6_relat_1(A_33) | ~r1_tarski(A_33, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_252])).
% 7.62/2.69  tff(c_463, plain, (![A_93, C_94, B_95]: (k3_xboole_0(A_93, k10_relat_1(C_94, B_95))=k10_relat_1(k7_relat_1(C_94, A_93), B_95) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.62/2.69  tff(c_479, plain, (![A_33, A_93]: (k10_relat_1(k7_relat_1(k6_relat_1(A_33), A_93), A_33)=k3_xboole_0(A_93, A_33) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_463])).
% 7.62/2.69  tff(c_491, plain, (![A_96, A_97]: (k10_relat_1(k7_relat_1(k6_relat_1(A_96), A_97), A_96)=k3_xboole_0(A_97, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_479])).
% 7.62/2.69  tff(c_503, plain, (![A_76, A_33]: (k3_xboole_0(A_76, A_33)=k10_relat_1(k6_relat_1(A_33), A_33) | ~r1_tarski(A_33, A_76))), inference(superposition, [status(thm), theory('equality')], [c_260, c_491])).
% 7.62/2.69  tff(c_517, plain, (![A_98, A_99]: (k3_xboole_0(A_98, A_99)=A_99 | ~r1_tarski(A_99, A_98))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_503])).
% 7.62/2.69  tff(c_532, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_50, c_517])).
% 7.62/2.69  tff(c_38, plain, (![B_35, A_34]: (r1_tarski(k1_relat_1(k7_relat_1(B_35, A_34)), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.62/2.69  tff(c_877, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k1_relat_1(k7_relat_1(B_120, A_119)))=k1_relat_1(k7_relat_1(B_120, A_119)) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_38, c_517])).
% 7.62/2.69  tff(c_895, plain, (![A_76, A_33]: (k3_xboole_0(A_76, k1_relat_1(k6_relat_1(A_33)))=k1_relat_1(k7_relat_1(k6_relat_1(A_33), A_76)) | ~v1_relat_1(k6_relat_1(A_33)) | ~r1_tarski(A_33, A_76))), inference(superposition, [status(thm), theory('equality')], [c_260, c_877])).
% 7.62/2.69  tff(c_911, plain, (![A_121, A_122]: (k1_relat_1(k7_relat_1(k6_relat_1(A_121), A_122))=k3_xboole_0(A_122, A_121) | ~r1_tarski(A_121, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_895])).
% 7.62/2.69  tff(c_530, plain, (![A_34, B_35]: (k3_xboole_0(A_34, k1_relat_1(k7_relat_1(B_35, A_34)))=k1_relat_1(k7_relat_1(B_35, A_34)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_38, c_517])).
% 7.62/2.69  tff(c_917, plain, (![A_122, A_121]: (k3_xboole_0(A_122, k3_xboole_0(A_122, A_121))=k1_relat_1(k7_relat_1(k6_relat_1(A_121), A_122)) | ~v1_relat_1(k6_relat_1(A_121)) | ~r1_tarski(A_121, A_122))), inference(superposition, [status(thm), theory('equality')], [c_911, c_530])).
% 7.62/2.69  tff(c_2196, plain, (![A_165, A_166]: (k3_xboole_0(A_165, k3_xboole_0(A_165, A_166))=k1_relat_1(k7_relat_1(k6_relat_1(A_166), A_165)) | ~r1_tarski(A_166, A_165))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_917])).
% 7.62/2.69  tff(c_2346, plain, (k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_2196])).
% 7.62/2.69  tff(c_2375, plain, (k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_532, c_2346])).
% 7.62/2.69  tff(c_261, plain, (![B_75]: (k7_relat_1(B_75, k1_relat_1(B_75))=B_75 | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_8, c_242])).
% 7.62/2.69  tff(c_2423, plain, (k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), '#skF_1')=k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2375, c_261])).
% 7.62/2.69  tff(c_2717, plain, (~v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_2423])).
% 7.62/2.69  tff(c_2720, plain, (~v1_relat_1(k6_relat_1('#skF_1')) | k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_584, c_2717])).
% 7.62/2.69  tff(c_2729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_42, c_2720])).
% 7.62/2.69  tff(c_2730, plain, (k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), '#skF_1')=k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2423])).
% 7.62/2.69  tff(c_2899, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k7_relat_1(k6_relat_1('#skF_1'), '#skF_1') | k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_584, c_2730])).
% 7.62/2.69  tff(c_2926, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_285, c_2899])).
% 7.62/2.69  tff(c_695, plain, (![A_113, B_114]: (k7_relat_1(A_113, k1_relat_1(k7_relat_1(B_114, k1_relat_1(A_113))))=k7_relat_1(A_113, k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.62/2.69  tff(c_757, plain, (![A_33, B_114]: (k7_relat_1(k6_relat_1(A_33), k1_relat_1(k7_relat_1(B_114, A_33)))=k7_relat_1(k6_relat_1(A_33), k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_695])).
% 7.62/2.69  tff(c_2929, plain, (![A_177, B_178]: (k7_relat_1(k6_relat_1(A_177), k1_relat_1(k7_relat_1(B_178, A_177)))=k7_relat_1(k6_relat_1(A_177), k1_relat_1(B_178)) | ~v1_relat_1(B_178))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_757])).
% 7.62/2.69  tff(c_2986, plain, (![A_177, B_178]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_177), k1_relat_1(B_178))), k1_relat_1(k7_relat_1(B_178, A_177))) | ~v1_relat_1(k6_relat_1(A_177)) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_2929, c_38])).
% 7.62/2.69  tff(c_3707, plain, (![A_191, B_192]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_191), k1_relat_1(B_192))), k1_relat_1(k7_relat_1(B_192, A_191))) | ~v1_relat_1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2986])).
% 7.62/2.69  tff(c_3729, plain, (r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2926, c_3707])).
% 7.62/2.69  tff(c_3847, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34, c_3729])).
% 7.62/2.69  tff(c_150, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(k7_relat_1(B_61, A_62)), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.62/2.69  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.62/2.69  tff(c_156, plain, (![B_61, A_62]: (k1_relat_1(k7_relat_1(B_61, A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(k7_relat_1(B_61, A_62))) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_150, c_4])).
% 7.62/2.69  tff(c_3895, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3847, c_156])).
% 7.62/2.69  tff(c_3912, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3895])).
% 7.62/2.69  tff(c_28, plain, (![B_28, A_27]: (k2_relat_1(k7_relat_1(B_28, A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.62/2.69  tff(c_5182, plain, (![A_201, B_202]: (k9_relat_1(A_201, k1_relat_1(k7_relat_1(B_202, k1_relat_1(A_201))))=k2_relat_1(k7_relat_1(A_201, k1_relat_1(B_202))) | ~v1_relat_1(A_201) | ~v1_relat_1(B_202) | ~v1_relat_1(A_201))), inference(superposition, [status(thm), theory('equality')], [c_695, c_28])).
% 7.62/2.69  tff(c_5215, plain, (k2_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))))=k9_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2926, c_5182])).
% 7.62/2.69  tff(c_5300, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42, c_52, c_34, c_34, c_5215])).
% 7.62/2.69  tff(c_30, plain, (![A_29]: (k10_relat_1(A_29, k2_relat_1(A_29))=k1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.62/2.69  tff(c_5342, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5300, c_30])).
% 7.62/2.69  tff(c_5352, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3912, c_5342])).
% 7.62/2.69  tff(c_12417, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5352])).
% 7.62/2.69  tff(c_12420, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_12417])).
% 7.62/2.69  tff(c_12424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_12420])).
% 7.62/2.69  tff(c_12425, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_5352])).
% 7.62/2.69  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.62/2.69  tff(c_469, plain, (![A_93, C_94, B_95]: (k5_xboole_0(A_93, k10_relat_1(k7_relat_1(C_94, A_93), B_95))=k4_xboole_0(A_93, k10_relat_1(C_94, B_95)) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_463, c_14])).
% 7.62/2.69  tff(c_12433, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12425, c_469])).
% 7.62/2.69  tff(c_12448, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_193, c_12433])).
% 7.62/2.69  tff(c_12450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_12448])).
% 7.62/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.69  
% 7.62/2.69  Inference rules
% 7.62/2.69  ----------------------
% 7.62/2.69  #Ref     : 0
% 7.62/2.69  #Sup     : 2853
% 7.62/2.69  #Fact    : 0
% 7.62/2.69  #Define  : 0
% 7.62/2.69  #Split   : 3
% 7.62/2.69  #Chain   : 0
% 7.62/2.69  #Close   : 0
% 7.62/2.69  
% 7.62/2.69  Ordering : KBO
% 7.62/2.69  
% 7.62/2.69  Simplification rules
% 7.62/2.69  ----------------------
% 7.62/2.69  #Subsume      : 472
% 7.62/2.69  #Demod        : 3623
% 7.62/2.69  #Tautology    : 1107
% 7.62/2.69  #SimpNegUnit  : 13
% 7.62/2.69  #BackRed      : 8
% 7.62/2.69  
% 7.62/2.69  #Partial instantiations: 0
% 7.62/2.69  #Strategies tried      : 1
% 7.62/2.69  
% 7.62/2.69  Timing (in seconds)
% 7.62/2.69  ----------------------
% 7.62/2.69  Preprocessing        : 0.32
% 7.62/2.69  Parsing              : 0.17
% 7.62/2.69  CNF conversion       : 0.02
% 7.62/2.69  Main loop            : 1.60
% 7.62/2.69  Inferencing          : 0.49
% 7.62/2.69  Reduction            : 0.62
% 7.62/2.69  Demodulation         : 0.49
% 7.62/2.69  BG Simplification    : 0.06
% 7.62/2.69  Subsumption          : 0.32
% 7.62/2.69  Abstraction          : 0.09
% 7.62/2.69  MUC search           : 0.00
% 7.62/2.69  Cooper               : 0.00
% 7.62/2.69  Total                : 1.95
% 7.62/2.69  Index Insertion      : 0.00
% 7.62/2.69  Index Deletion       : 0.00
% 7.62/2.69  Index Matching       : 0.00
% 7.62/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
