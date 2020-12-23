%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  104 (2344 expanded)
%              Number of leaves         :   42 ( 805 expanded)
%              Depth                    :   17
%              Number of atoms          :   92 (2341 expanded)
%              Number of equality atoms :   68 (2304 expanded)
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

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_83,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_82,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_147,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,A_68) = k5_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_163,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_22])).

tff(c_26,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_744,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_832,plain,(
    ! [A_20,C_111] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_744])).

tff(c_847,plain,(
    ! [A_20,C_111] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_832])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_880,plain,(
    ! [A_113,C_114] : k5_xboole_0(A_113,k5_xboole_0(A_113,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_832])).

tff(c_963,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k5_xboole_0(B_120,A_119)) = B_120 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_880])).

tff(c_999,plain,(
    ! [A_20,C_111] : k5_xboole_0(k5_xboole_0(A_20,C_111),C_111) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_963])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_464,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_493,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_464])).

tff(c_28,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_791,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k5_xboole_0(B_22,k3_xboole_0(A_21,B_22))) = k2_xboole_0(A_21,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_744])).

tff(c_1306,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k4_xboole_0(B_133,A_132)) = k2_xboole_0(A_132,B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_791])).

tff(c_1445,plain,(
    ! [A_139,B_140] : k5_xboole_0(A_139,k2_xboole_0(A_139,B_140)) = k4_xboole_0(B_140,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_847])).

tff(c_1497,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1445])).

tff(c_1506,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1497])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1530,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_20])).

tff(c_1535,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1530])).

tff(c_1540,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = k2_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_28])).

tff(c_1549,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1540])).

tff(c_919,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k4_xboole_0(B_4,A_3)) = k3_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_880])).

tff(c_1524,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_919])).

tff(c_1533,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1524])).

tff(c_1561,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1533])).

tff(c_1580,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k3_xboole_0('#skF_4',k1_tarski('#skF_3'))) = k2_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_28])).

tff(c_1584,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_26,c_1535,c_1580])).

tff(c_60,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1605,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1584,c_60])).

tff(c_18,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_253,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_261,plain,(
    ! [A_13] : k3_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_253])).

tff(c_471,plain,(
    ! [B_95] : k4_xboole_0(k1_xboole_0,B_95) = k3_xboole_0(k1_xboole_0,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_163])).

tff(c_495,plain,(
    ! [B_95] : k4_xboole_0(k1_xboole_0,B_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_471])).

tff(c_1591,plain,(
    ! [B_95] : k4_xboole_0('#skF_4',B_95) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1584,c_495])).

tff(c_1686,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1506])).

tff(c_260,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_12,c_253])).

tff(c_635,plain,(
    ! [A_104,B_105] : k5_xboole_0(k5_xboole_0(A_104,B_105),k3_xboole_0(A_104,B_105)) = k2_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_695,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_20,A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_635])).

tff(c_705,plain,(
    ! [A_20] : k2_xboole_0(A_20,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_260,c_695])).

tff(c_30,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_302,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_311,plain,(
    ! [A_23] : k3_tarski(k1_tarski(A_23)) = k2_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_302])).

tff(c_706,plain,(
    ! [A_23] : k3_tarski(k1_tarski(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_311])).

tff(c_1738,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_706])).

tff(c_1741,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_1738])).

tff(c_1743,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1686])).

tff(c_58,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_381,plain,(
    ! [C_82,A_83] :
      ( r2_hidden(C_82,k1_zfmisc_1(A_83))
      | ~ r1_tarski(C_82,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_389,plain,(
    ! [C_82] :
      ( r2_hidden(C_82,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_381])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_393,plain,(
    ! [A_85,C_86] :
      ( ~ r2_hidden(k1_zfmisc_1(A_85),C_86)
      | ~ r1_tarski(C_86,A_85) ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_438,plain,(
    ! [C_91] :
      ( ~ r2_hidden(k1_tarski(k1_xboole_0),C_91)
      | ~ r1_tarski(C_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_393])).

tff(c_447,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_389,c_438])).

tff(c_1592,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1584,c_447])).

tff(c_1838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1743,c_1592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.56  
% 3.59/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.56  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.59/1.56  
% 3.59/1.56  %Foreground sorts:
% 3.59/1.56  
% 3.59/1.56  
% 3.59/1.56  %Background operators:
% 3.59/1.56  
% 3.59/1.56  
% 3.59/1.56  %Foreground operators:
% 3.59/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.59/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.59/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.59/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.59/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.59/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.59/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.59/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/1.56  
% 3.59/1.58  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.59/1.58  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.59/1.58  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.59/1.58  tff(f_56, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.59/1.58  tff(f_54, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.59/1.58  tff(f_87, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.59/1.58  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.59/1.58  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.59/1.58  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.59/1.58  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.59/1.58  tff(f_83, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.59/1.58  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.59/1.58  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.59/1.58  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.59/1.58  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.59/1.58  tff(f_82, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.59/1.58  tff(f_79, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.59/1.58  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.59/1.58  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.59/1.58  tff(c_147, plain, (![B_67, A_68]: (k5_xboole_0(B_67, A_68)=k5_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.59/1.58  tff(c_22, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.59/1.58  tff(c_163, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_147, c_22])).
% 3.59/1.58  tff(c_26, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.58  tff(c_744, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.59/1.58  tff(c_832, plain, (![A_20, C_111]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_26, c_744])).
% 3.59/1.58  tff(c_847, plain, (![A_20, C_111]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_832])).
% 3.59/1.58  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.59/1.58  tff(c_880, plain, (![A_113, C_114]: (k5_xboole_0(A_113, k5_xboole_0(A_113, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_832])).
% 3.59/1.58  tff(c_963, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k5_xboole_0(B_120, A_119))=B_120)), inference(superposition, [status(thm), theory('equality')], [c_6, c_880])).
% 3.59/1.58  tff(c_999, plain, (![A_20, C_111]: (k5_xboole_0(k5_xboole_0(A_20, C_111), C_111)=A_20)), inference(superposition, [status(thm), theory('equality')], [c_847, c_963])).
% 3.59/1.58  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.58  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.58  tff(c_464, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.59/1.58  tff(c_493, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_464])).
% 3.59/1.58  tff(c_28, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.59/1.58  tff(c_791, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k5_xboole_0(B_22, k3_xboole_0(A_21, B_22)))=k2_xboole_0(A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_28, c_744])).
% 3.59/1.58  tff(c_1306, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k4_xboole_0(B_133, A_132))=k2_xboole_0(A_132, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_791])).
% 3.59/1.58  tff(c_1445, plain, (![A_139, B_140]: (k5_xboole_0(A_139, k2_xboole_0(A_139, B_140))=k4_xboole_0(B_140, A_139))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_847])).
% 3.59/1.58  tff(c_1497, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1445])).
% 3.59/1.58  tff(c_1506, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1497])).
% 3.59/1.58  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.59/1.58  tff(c_1530, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1506, c_20])).
% 3.59/1.58  tff(c_1535, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1530])).
% 3.59/1.58  tff(c_1540, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))=k2_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1535, c_28])).
% 3.59/1.58  tff(c_1549, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_999, c_1540])).
% 3.59/1.58  tff(c_919, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k4_xboole_0(B_4, A_3))=k3_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_493, c_880])).
% 3.59/1.58  tff(c_1524, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1506, c_919])).
% 3.59/1.58  tff(c_1533, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1524])).
% 3.59/1.58  tff(c_1561, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1533])).
% 3.59/1.58  tff(c_1580, plain, (k5_xboole_0(k1_tarski('#skF_3'), k3_xboole_0('#skF_4', k1_tarski('#skF_3')))=k2_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_28])).
% 3.59/1.58  tff(c_1584, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_26, c_1535, c_1580])).
% 3.59/1.58  tff(c_60, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.59/1.58  tff(c_1605, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1584, c_60])).
% 3.59/1.58  tff(c_18, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.58  tff(c_253, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.59/1.58  tff(c_261, plain, (![A_13]: (k3_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_253])).
% 3.59/1.58  tff(c_471, plain, (![B_95]: (k4_xboole_0(k1_xboole_0, B_95)=k3_xboole_0(k1_xboole_0, B_95))), inference(superposition, [status(thm), theory('equality')], [c_464, c_163])).
% 3.59/1.58  tff(c_495, plain, (![B_95]: (k4_xboole_0(k1_xboole_0, B_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_471])).
% 3.59/1.58  tff(c_1591, plain, (![B_95]: (k4_xboole_0('#skF_4', B_95)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1584, c_495])).
% 3.59/1.58  tff(c_1686, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1506])).
% 3.59/1.58  tff(c_260, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_12, c_253])).
% 3.59/1.58  tff(c_635, plain, (![A_104, B_105]: (k5_xboole_0(k5_xboole_0(A_104, B_105), k3_xboole_0(A_104, B_105))=k2_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.59/1.58  tff(c_695, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_20, A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_26, c_635])).
% 3.59/1.58  tff(c_705, plain, (![A_20]: (k2_xboole_0(A_20, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_260, c_695])).
% 3.59/1.58  tff(c_30, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.59/1.58  tff(c_302, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.59/1.58  tff(c_311, plain, (![A_23]: (k3_tarski(k1_tarski(A_23))=k2_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_30, c_302])).
% 3.59/1.58  tff(c_706, plain, (![A_23]: (k3_tarski(k1_tarski(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_705, c_311])).
% 3.59/1.58  tff(c_1738, plain, (k3_tarski('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1686, c_706])).
% 3.59/1.58  tff(c_1741, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_1738])).
% 3.59/1.58  tff(c_1743, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1686])).
% 3.59/1.58  tff(c_58, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.58  tff(c_381, plain, (![C_82, A_83]: (r2_hidden(C_82, k1_zfmisc_1(A_83)) | ~r1_tarski(C_82, A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.58  tff(c_389, plain, (![C_82]: (r2_hidden(C_82, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_381])).
% 3.59/1.58  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.59/1.58  tff(c_393, plain, (![A_85, C_86]: (~r2_hidden(k1_zfmisc_1(A_85), C_86) | ~r1_tarski(C_86, A_85))), inference(resolution, [status(thm)], [c_381, c_2])).
% 3.59/1.58  tff(c_438, plain, (![C_91]: (~r2_hidden(k1_tarski(k1_xboole_0), C_91) | ~r1_tarski(C_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_393])).
% 3.59/1.58  tff(c_447, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_389, c_438])).
% 3.59/1.58  tff(c_1592, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1584, c_447])).
% 3.59/1.58  tff(c_1838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1743, c_1592])).
% 3.59/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.58  
% 3.59/1.58  Inference rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Ref     : 0
% 3.59/1.58  #Sup     : 436
% 3.59/1.58  #Fact    : 0
% 3.59/1.58  #Define  : 0
% 3.59/1.58  #Split   : 0
% 3.59/1.58  #Chain   : 0
% 3.59/1.58  #Close   : 0
% 3.59/1.58  
% 3.59/1.58  Ordering : KBO
% 3.59/1.58  
% 3.59/1.58  Simplification rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Subsume      : 6
% 3.59/1.58  #Demod        : 249
% 3.59/1.58  #Tautology    : 289
% 3.59/1.58  #SimpNegUnit  : 0
% 3.59/1.58  #BackRed      : 27
% 3.59/1.58  
% 3.59/1.58  #Partial instantiations: 0
% 3.59/1.58  #Strategies tried      : 1
% 3.59/1.58  
% 3.59/1.58  Timing (in seconds)
% 3.59/1.58  ----------------------
% 3.59/1.58  Preprocessing        : 0.34
% 3.59/1.59  Parsing              : 0.18
% 3.59/1.59  CNF conversion       : 0.02
% 3.59/1.59  Main loop            : 0.47
% 3.59/1.59  Inferencing          : 0.16
% 3.59/1.59  Reduction            : 0.19
% 3.59/1.59  Demodulation         : 0.15
% 3.59/1.59  BG Simplification    : 0.03
% 3.59/1.59  Subsumption          : 0.07
% 3.59/1.59  Abstraction          : 0.03
% 3.59/1.59  MUC search           : 0.00
% 3.59/1.59  Cooper               : 0.00
% 3.59/1.59  Total                : 0.85
% 3.59/1.59  Index Insertion      : 0.00
% 3.59/1.59  Index Deletion       : 0.00
% 3.59/1.59  Index Matching       : 0.00
% 3.59/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
