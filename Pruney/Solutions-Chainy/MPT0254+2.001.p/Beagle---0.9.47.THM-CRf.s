%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 564 expanded)
%              Number of leaves         :   43 ( 210 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 ( 573 expanded)
%              Number of equality atoms :   67 ( 509 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_85,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_14,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_466,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_491,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_466])).

tff(c_961,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k3_xboole_0(A_118,B_119)) = k2_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_979,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k5_xboole_0(B_119,k3_xboole_0(A_118,B_119))) = k2_xboole_0(A_118,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_26])).

tff(c_1406,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k4_xboole_0(B_135,A_134)) = k2_xboole_0(A_134,B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_979])).

tff(c_126,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,A_71) = k5_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_24])).

tff(c_28,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_721,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_796,plain,(
    ! [A_22,C_113] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_113)) = k5_xboole_0(k1_xboole_0,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_721])).

tff(c_809,plain,(
    ! [A_22,C_113] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_113)) = C_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_796])).

tff(c_1519,plain,(
    ! [A_143,B_144] : k5_xboole_0(A_143,k2_xboole_0(A_143,B_144)) = k4_xboole_0(B_144,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_809])).

tff(c_1574,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1519])).

tff(c_1586,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1574])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_810,plain,(
    ! [A_114,C_115] : k5_xboole_0(A_114,k5_xboole_0(A_114,C_115)) = C_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_796])).

tff(c_856,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k5_xboole_0(B_6,A_5)) = B_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_810])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_265,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_275,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k4_xboole_0(A_16,B_17) ),
    inference(resolution,[status(thm)],[c_22,c_265])).

tff(c_1010,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_16,B_17),A_16),k4_xboole_0(A_16,B_17)) = k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_961])).

tff(c_1056,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_6,c_6,c_1010])).

tff(c_1597,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_1056])).

tff(c_1664,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1597,c_64])).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1693,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_62])).

tff(c_20,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_277,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_1019,plain,(
    ! [A_15] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_15),k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_961])).

tff(c_1058,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_142,c_1019])).

tff(c_1710,plain,(
    ! [A_151] : k2_xboole_0('#skF_4',A_151) = A_151 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1058])).

tff(c_575,plain,(
    ! [A_105,B_106] : k3_xboole_0(k4_xboole_0(A_105,B_106),A_105) = k4_xboole_0(A_105,B_106) ),
    inference(resolution,[status(thm)],[c_22,c_265])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_581,plain,(
    ! [A_105,B_106] : k5_xboole_0(k4_xboole_0(A_105,B_106),k4_xboole_0(A_105,B_106)) = k4_xboole_0(k4_xboole_0(A_105,B_106),A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_16])).

tff(c_617,plain,(
    ! [A_105,B_106] : k4_xboole_0(k4_xboole_0(A_105,B_106),A_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_581])).

tff(c_1445,plain,(
    ! [A_105,B_106] : k2_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = k5_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_1406])).

tff(c_1462,plain,(
    ! [A_105,B_106] : k2_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1445])).

tff(c_1591,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_1462])).

tff(c_1716,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_1591])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_367,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_376,plain,(
    ! [A_25] : k3_tarski(k1_tarski(A_25)) = k2_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_367])).

tff(c_379,plain,(
    ! [A_25] : k3_tarski(k1_tarski(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_376])).

tff(c_1756,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_379])).

tff(c_1759,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1756])).

tff(c_1733,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1591,c_1710])).

tff(c_1783,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1733])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_390,plain,(
    ! [C_87,A_88] :
      ( r2_hidden(C_87,k1_zfmisc_1(A_88))
      | ~ r1_tarski(C_87,A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_398,plain,(
    ! [C_87] :
      ( r2_hidden(C_87,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_390])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_444,plain,(
    ! [A_94,C_95] :
      ( ~ r2_hidden(k1_zfmisc_1(A_94),C_95)
      | ~ r1_tarski(C_95,A_94) ) ),
    inference(resolution,[status(thm)],[c_390,c_2])).

tff(c_555,plain,(
    ! [C_101] :
      ( ~ r2_hidden(k1_tarski(k1_xboole_0),C_101)
      | ~ r1_tarski(C_101,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_444])).

tff(c_564,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_398,c_555])).

tff(c_1678,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_564])).

tff(c_2005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1783,c_1678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.63  
% 3.70/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.64  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.70/1.64  
% 3.70/1.64  %Foreground sorts:
% 3.70/1.64  
% 3.70/1.64  
% 3.70/1.64  %Background operators:
% 3.70/1.64  
% 3.70/1.64  
% 3.70/1.64  %Foreground operators:
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.70/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.70/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.70/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.70/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.70/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.70/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.70/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.64  
% 3.70/1.65  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.65  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.70/1.65  tff(f_89, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.70/1.65  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.70/1.65  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.70/1.65  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.70/1.65  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.70/1.65  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.70/1.65  tff(f_58, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.70/1.65  tff(f_52, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.70/1.65  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.70/1.65  tff(f_85, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.70/1.65  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.70/1.65  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.70/1.66  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.70/1.66  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.70/1.66  tff(f_84, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.70/1.66  tff(f_81, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.70/1.66  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.70/1.66  tff(c_14, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.70/1.66  tff(c_24, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.70/1.66  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.70/1.66  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.66  tff(c_466, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.66  tff(c_491, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_466])).
% 3.70/1.66  tff(c_961, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k3_xboole_0(A_118, B_119))=k2_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/1.66  tff(c_26, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.66  tff(c_979, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k5_xboole_0(B_119, k3_xboole_0(A_118, B_119)))=k2_xboole_0(A_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_961, c_26])).
% 3.70/1.66  tff(c_1406, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k4_xboole_0(B_135, A_134))=k2_xboole_0(A_134, B_135))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_979])).
% 3.70/1.66  tff(c_126, plain, (![B_70, A_71]: (k5_xboole_0(B_70, A_71)=k5_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.66  tff(c_142, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_126, c_24])).
% 3.70/1.66  tff(c_28, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.66  tff(c_721, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.66  tff(c_796, plain, (![A_22, C_113]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_113))=k5_xboole_0(k1_xboole_0, C_113))), inference(superposition, [status(thm), theory('equality')], [c_28, c_721])).
% 3.70/1.66  tff(c_809, plain, (![A_22, C_113]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_113))=C_113)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_796])).
% 3.70/1.66  tff(c_1519, plain, (![A_143, B_144]: (k5_xboole_0(A_143, k2_xboole_0(A_143, B_144))=k4_xboole_0(B_144, A_143))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_809])).
% 3.70/1.66  tff(c_1574, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1519])).
% 3.70/1.66  tff(c_1586, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1574])).
% 3.70/1.66  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.66  tff(c_810, plain, (![A_114, C_115]: (k5_xboole_0(A_114, k5_xboole_0(A_114, C_115))=C_115)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_796])).
% 3.70/1.66  tff(c_856, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k5_xboole_0(B_6, A_5))=B_6)), inference(superposition, [status(thm), theory('equality')], [c_6, c_810])).
% 3.70/1.66  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/1.66  tff(c_265, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.70/1.66  tff(c_275, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k4_xboole_0(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_265])).
% 3.70/1.66  tff(c_1010, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_16, B_17), A_16), k4_xboole_0(A_16, B_17))=k2_xboole_0(k4_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_275, c_961])).
% 3.70/1.66  tff(c_1056, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_6, c_6, c_1010])).
% 3.70/1.66  tff(c_1597, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1586, c_1056])).
% 3.70/1.66  tff(c_1664, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1597, c_64])).
% 3.70/1.66  tff(c_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.66  tff(c_1693, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_62])).
% 3.70/1.66  tff(c_20, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.70/1.66  tff(c_277, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_265])).
% 3.70/1.66  tff(c_1019, plain, (![A_15]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_15), k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_277, c_961])).
% 3.70/1.66  tff(c_1058, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_142, c_1019])).
% 3.70/1.66  tff(c_1710, plain, (![A_151]: (k2_xboole_0('#skF_4', A_151)=A_151)), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1058])).
% 3.70/1.66  tff(c_575, plain, (![A_105, B_106]: (k3_xboole_0(k4_xboole_0(A_105, B_106), A_105)=k4_xboole_0(A_105, B_106))), inference(resolution, [status(thm)], [c_22, c_265])).
% 3.70/1.66  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.66  tff(c_581, plain, (![A_105, B_106]: (k5_xboole_0(k4_xboole_0(A_105, B_106), k4_xboole_0(A_105, B_106))=k4_xboole_0(k4_xboole_0(A_105, B_106), A_105))), inference(superposition, [status(thm), theory('equality')], [c_575, c_16])).
% 3.70/1.66  tff(c_617, plain, (![A_105, B_106]: (k4_xboole_0(k4_xboole_0(A_105, B_106), A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_581])).
% 3.70/1.66  tff(c_1445, plain, (![A_105, B_106]: (k2_xboole_0(A_105, k4_xboole_0(A_105, B_106))=k5_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_617, c_1406])).
% 3.70/1.66  tff(c_1462, plain, (![A_105, B_106]: (k2_xboole_0(A_105, k4_xboole_0(A_105, B_106))=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1445])).
% 3.70/1.66  tff(c_1591, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1586, c_1462])).
% 3.70/1.66  tff(c_1716, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1710, c_1591])).
% 3.70/1.66  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.70/1.66  tff(c_32, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.70/1.66  tff(c_367, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.66  tff(c_376, plain, (![A_25]: (k3_tarski(k1_tarski(A_25))=k2_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_32, c_367])).
% 3.70/1.66  tff(c_379, plain, (![A_25]: (k3_tarski(k1_tarski(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_376])).
% 3.70/1.66  tff(c_1756, plain, (k3_tarski('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1716, c_379])).
% 3.70/1.66  tff(c_1759, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1756])).
% 3.70/1.66  tff(c_1733, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1591, c_1710])).
% 3.70/1.66  tff(c_1783, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1733])).
% 3.70/1.66  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.70/1.66  tff(c_390, plain, (![C_87, A_88]: (r2_hidden(C_87, k1_zfmisc_1(A_88)) | ~r1_tarski(C_87, A_88))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.70/1.66  tff(c_398, plain, (![C_87]: (r2_hidden(C_87, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_390])).
% 3.70/1.66  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.70/1.66  tff(c_444, plain, (![A_94, C_95]: (~r2_hidden(k1_zfmisc_1(A_94), C_95) | ~r1_tarski(C_95, A_94))), inference(resolution, [status(thm)], [c_390, c_2])).
% 3.70/1.66  tff(c_555, plain, (![C_101]: (~r2_hidden(k1_tarski(k1_xboole_0), C_101) | ~r1_tarski(C_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_444])).
% 3.70/1.66  tff(c_564, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_398, c_555])).
% 3.70/1.66  tff(c_1678, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_564])).
% 3.70/1.66  tff(c_2005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1783, c_1678])).
% 3.70/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  Inference rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Ref     : 0
% 3.70/1.66  #Sup     : 475
% 3.70/1.66  #Fact    : 0
% 3.70/1.66  #Define  : 0
% 3.70/1.66  #Split   : 0
% 3.70/1.66  #Chain   : 0
% 3.70/1.66  #Close   : 0
% 3.70/1.66  
% 3.70/1.66  Ordering : KBO
% 3.70/1.66  
% 3.70/1.66  Simplification rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Subsume      : 6
% 3.70/1.66  #Demod        : 283
% 3.70/1.66  #Tautology    : 317
% 3.70/1.66  #SimpNegUnit  : 0
% 3.70/1.66  #BackRed      : 27
% 3.70/1.66  
% 3.70/1.66  #Partial instantiations: 0
% 3.70/1.66  #Strategies tried      : 1
% 3.70/1.66  
% 3.70/1.66  Timing (in seconds)
% 3.70/1.66  ----------------------
% 3.70/1.66  Preprocessing        : 0.33
% 3.70/1.66  Parsing              : 0.18
% 3.70/1.66  CNF conversion       : 0.02
% 3.70/1.66  Main loop            : 0.55
% 3.70/1.66  Inferencing          : 0.19
% 3.70/1.66  Reduction            : 0.21
% 3.70/1.66  Demodulation         : 0.17
% 3.70/1.66  BG Simplification    : 0.03
% 3.70/1.66  Subsumption          : 0.08
% 3.70/1.66  Abstraction          : 0.03
% 3.70/1.66  MUC search           : 0.00
% 3.70/1.66  Cooper               : 0.00
% 3.70/1.66  Total                : 0.92
% 3.70/1.66  Index Insertion      : 0.00
% 3.70/1.66  Index Deletion       : 0.00
% 3.70/1.66  Index Matching       : 0.00
% 3.70/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
