%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:20 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  111 (4537 expanded)
%              Number of leaves         :   42 (1543 expanded)
%              Depth                    :   20
%              Number of atoms          :   99 (4547 expanded)
%              Number of equality atoms :   75 (4482 expanded)
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

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_85,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_81,axiom,(
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

tff(c_146,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,A_71) = k5_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = A_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_28,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_828,plain,(
    ! [A_115,B_116,C_117] : k5_xboole_0(k5_xboole_0(A_115,B_116),C_117) = k5_xboole_0(A_115,k5_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_916,plain,(
    ! [A_21,C_117] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_117)) = k5_xboole_0(k1_xboole_0,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_828])).

tff(c_931,plain,(
    ! [A_21,C_117] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_117)) = C_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_916])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_955,plain,(
    ! [A_124,C_125] : k5_xboole_0(A_124,k5_xboole_0(A_124,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_916])).

tff(c_1029,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k5_xboole_0(B_127,A_126)) = B_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_955])).

tff(c_1065,plain,(
    ! [A_21,C_117] : k5_xboole_0(k5_xboole_0(A_21,C_117),C_117) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1029])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_462,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_478,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_462])).

tff(c_30,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_875,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k5_xboole_0(B_23,k3_xboole_0(A_22,B_23))) = k2_xboole_0(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_828])).

tff(c_1372,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k4_xboole_0(B_137,A_136)) = k2_xboole_0(A_136,B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_875])).

tff(c_1444,plain,(
    ! [A_143,B_144] : k5_xboole_0(A_143,k2_xboole_0(A_143,B_144)) = k4_xboole_0(B_144,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_931])).

tff(c_1496,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1444])).

tff(c_1505,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1496])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1512,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_22])).

tff(c_1516,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_1512])).

tff(c_1521,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = k2_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_30])).

tff(c_1536,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1521])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1527,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_14])).

tff(c_1538,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_1527])).

tff(c_1583,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k3_xboole_0('#skF_4',k1_tarski('#skF_3'))) = k2_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_30])).

tff(c_1587,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_28,c_1516,c_1583])).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1624,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1587,c_62])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [B_12] : k3_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_103])).

tff(c_1618,plain,(
    ! [B_12] : k3_xboole_0('#skF_4',B_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1587,c_116])).

tff(c_1663,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1516])).

tff(c_241,plain,(
    ! [B_73,A_74] : k3_xboole_0(B_73,A_74) = k3_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_257,plain,(
    ! [B_73] : k3_xboole_0(B_73,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_116])).

tff(c_475,plain,(
    ! [B_73] : k5_xboole_0(B_73,k1_xboole_0) = k4_xboole_0(B_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_462])).

tff(c_492,plain,(
    ! [B_73] : k4_xboole_0(B_73,k1_xboole_0) = B_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_475])).

tff(c_534,plain,(
    ! [B_99] : k4_xboole_0(B_99,k1_xboole_0) = B_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_475])).

tff(c_544,plain,(
    ! [B_99] : k4_xboole_0(B_99,B_99) = k3_xboole_0(B_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_22])).

tff(c_557,plain,(
    ! [B_100] : k4_xboole_0(B_100,B_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_544])).

tff(c_569,plain,(
    ! [B_100] : k4_xboole_0(B_100,k1_xboole_0) = k3_xboole_0(B_100,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_22])).

tff(c_582,plain,(
    ! [B_100] : k3_xboole_0(B_100,B_100) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_569])).

tff(c_697,plain,(
    ! [A_110,B_111] : k5_xboole_0(k5_xboole_0(A_110,B_111),k3_xboole_0(A_110,B_111)) = k2_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_757,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_21,A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_697])).

tff(c_767,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_582,c_757])).

tff(c_32,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_364,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_373,plain,(
    ! [A_24] : k3_tarski(k1_tarski(A_24)) = k2_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_364])).

tff(c_798,plain,(
    ! [A_24] : k3_tarski(k1_tarski(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_373])).

tff(c_1724,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_798])).

tff(c_1727,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1724])).

tff(c_1729,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_1663])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1620,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1587,c_60])).

tff(c_1734,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1620])).

tff(c_48,plain,(
    ! [C_56,A_52] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_56,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_393,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(C_83,k1_zfmisc_1(A_84))
      | ~ r1_tarski(C_83,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_429,plain,(
    ! [A_90,C_91] :
      ( ~ r2_hidden(k1_zfmisc_1(A_90),C_91)
      | ~ r1_tarski(C_91,A_90) ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_690,plain,(
    ! [A_108,A_109] :
      ( ~ r1_tarski(k1_zfmisc_1(A_108),A_109)
      | ~ r1_tarski(k1_zfmisc_1(A_109),A_108) ) ),
    inference(resolution,[status(thm)],[c_48,c_429])).

tff(c_696,plain,(
    ! [A_108] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(A_108)),A_108) ),
    inference(resolution,[status(thm)],[c_12,c_690])).

tff(c_1751,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_696])).

tff(c_1767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1734,c_1751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.66  
% 3.37/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.66  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.37/1.66  
% 3.37/1.66  %Foreground sorts:
% 3.37/1.66  
% 3.37/1.66  
% 3.37/1.66  %Background operators:
% 3.37/1.66  
% 3.37/1.66  
% 3.37/1.66  %Foreground operators:
% 3.37/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.37/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.37/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.66  
% 3.44/1.68  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.68  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.44/1.68  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.44/1.68  tff(f_58, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.44/1.68  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.44/1.68  tff(f_89, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.44/1.68  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.68  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.68  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.44/1.68  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.44/1.68  tff(f_85, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.44/1.68  tff(f_44, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.44/1.68  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.44/1.68  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.68  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.44/1.68  tff(f_84, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.44/1.68  tff(f_81, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.44/1.68  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.44/1.68  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.68  tff(c_146, plain, (![B_70, A_71]: (k5_xboole_0(B_70, A_71)=k5_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.68  tff(c_24, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.68  tff(c_162, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=A_71)), inference(superposition, [status(thm), theory('equality')], [c_146, c_24])).
% 3.44/1.68  tff(c_28, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.68  tff(c_828, plain, (![A_115, B_116, C_117]: (k5_xboole_0(k5_xboole_0(A_115, B_116), C_117)=k5_xboole_0(A_115, k5_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.68  tff(c_916, plain, (![A_21, C_117]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_117))=k5_xboole_0(k1_xboole_0, C_117))), inference(superposition, [status(thm), theory('equality')], [c_28, c_828])).
% 3.44/1.68  tff(c_931, plain, (![A_21, C_117]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_117))=C_117)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_916])).
% 3.44/1.68  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.68  tff(c_955, plain, (![A_124, C_125]: (k5_xboole_0(A_124, k5_xboole_0(A_124, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_916])).
% 3.44/1.68  tff(c_1029, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k5_xboole_0(B_127, A_126))=B_127)), inference(superposition, [status(thm), theory('equality')], [c_6, c_955])).
% 3.44/1.68  tff(c_1065, plain, (![A_21, C_117]: (k5_xboole_0(k5_xboole_0(A_21, C_117), C_117)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_931, c_1029])).
% 3.44/1.68  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.44/1.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.68  tff(c_462, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.68  tff(c_478, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_462])).
% 3.44/1.68  tff(c_30, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.44/1.68  tff(c_875, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k5_xboole_0(B_23, k3_xboole_0(A_22, B_23)))=k2_xboole_0(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_30, c_828])).
% 3.44/1.68  tff(c_1372, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k4_xboole_0(B_137, A_136))=k2_xboole_0(A_136, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_875])).
% 3.44/1.68  tff(c_1444, plain, (![A_143, B_144]: (k5_xboole_0(A_143, k2_xboole_0(A_143, B_144))=k4_xboole_0(B_144, A_143))), inference(superposition, [status(thm), theory('equality')], [c_1372, c_931])).
% 3.44/1.68  tff(c_1496, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1444])).
% 3.44/1.68  tff(c_1505, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1496])).
% 3.44/1.68  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.44/1.68  tff(c_1512, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_22])).
% 3.44/1.68  tff(c_1516, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_1512])).
% 3.44/1.68  tff(c_1521, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))=k2_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_30])).
% 3.44/1.68  tff(c_1536, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_1521])).
% 3.44/1.68  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.68  tff(c_1527, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1516, c_14])).
% 3.44/1.68  tff(c_1538, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_1527])).
% 3.44/1.68  tff(c_1583, plain, (k5_xboole_0(k1_tarski('#skF_3'), k3_xboole_0('#skF_4', k1_tarski('#skF_3')))=k2_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1538, c_30])).
% 3.44/1.68  tff(c_1587, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_28, c_1516, c_1583])).
% 3.44/1.68  tff(c_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.44/1.68  tff(c_1624, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1587, c_62])).
% 3.44/1.68  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.68  tff(c_103, plain, (![A_65]: (k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.68  tff(c_116, plain, (![B_12]: (k3_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_103])).
% 3.44/1.68  tff(c_1618, plain, (![B_12]: (k3_xboole_0('#skF_4', B_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1587, c_116])).
% 3.44/1.68  tff(c_1663, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1516])).
% 3.44/1.68  tff(c_241, plain, (![B_73, A_74]: (k3_xboole_0(B_73, A_74)=k3_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.68  tff(c_257, plain, (![B_73]: (k3_xboole_0(B_73, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_241, c_116])).
% 3.44/1.68  tff(c_475, plain, (![B_73]: (k5_xboole_0(B_73, k1_xboole_0)=k4_xboole_0(B_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_257, c_462])).
% 3.44/1.68  tff(c_492, plain, (![B_73]: (k4_xboole_0(B_73, k1_xboole_0)=B_73)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_475])).
% 3.44/1.68  tff(c_534, plain, (![B_99]: (k4_xboole_0(B_99, k1_xboole_0)=B_99)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_475])).
% 3.44/1.68  tff(c_544, plain, (![B_99]: (k4_xboole_0(B_99, B_99)=k3_xboole_0(B_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_534, c_22])).
% 3.44/1.68  tff(c_557, plain, (![B_100]: (k4_xboole_0(B_100, B_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_544])).
% 3.44/1.68  tff(c_569, plain, (![B_100]: (k4_xboole_0(B_100, k1_xboole_0)=k3_xboole_0(B_100, B_100))), inference(superposition, [status(thm), theory('equality')], [c_557, c_22])).
% 3.44/1.68  tff(c_582, plain, (![B_100]: (k3_xboole_0(B_100, B_100)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_492, c_569])).
% 3.44/1.68  tff(c_697, plain, (![A_110, B_111]: (k5_xboole_0(k5_xboole_0(A_110, B_111), k3_xboole_0(A_110, B_111))=k2_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.44/1.68  tff(c_757, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_21, A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_28, c_697])).
% 3.44/1.68  tff(c_767, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_582, c_757])).
% 3.44/1.68  tff(c_32, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.68  tff(c_364, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.44/1.68  tff(c_373, plain, (![A_24]: (k3_tarski(k1_tarski(A_24))=k2_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_32, c_364])).
% 3.44/1.68  tff(c_798, plain, (![A_24]: (k3_tarski(k1_tarski(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_767, c_373])).
% 3.44/1.68  tff(c_1724, plain, (k3_tarski('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1663, c_798])).
% 3.44/1.68  tff(c_1727, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1724])).
% 3.44/1.68  tff(c_1729, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1727, c_1663])).
% 3.44/1.68  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.68  tff(c_1620, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1587, c_60])).
% 3.44/1.68  tff(c_1734, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1620])).
% 3.44/1.68  tff(c_48, plain, (![C_56, A_52]: (r2_hidden(C_56, k1_zfmisc_1(A_52)) | ~r1_tarski(C_56, A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.68  tff(c_393, plain, (![C_83, A_84]: (r2_hidden(C_83, k1_zfmisc_1(A_84)) | ~r1_tarski(C_83, A_84))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.68  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.44/1.68  tff(c_429, plain, (![A_90, C_91]: (~r2_hidden(k1_zfmisc_1(A_90), C_91) | ~r1_tarski(C_91, A_90))), inference(resolution, [status(thm)], [c_393, c_2])).
% 3.44/1.68  tff(c_690, plain, (![A_108, A_109]: (~r1_tarski(k1_zfmisc_1(A_108), A_109) | ~r1_tarski(k1_zfmisc_1(A_109), A_108))), inference(resolution, [status(thm)], [c_48, c_429])).
% 3.44/1.68  tff(c_696, plain, (![A_108]: (~r1_tarski(k1_zfmisc_1(k1_zfmisc_1(A_108)), A_108))), inference(resolution, [status(thm)], [c_12, c_690])).
% 3.44/1.68  tff(c_1751, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1734, c_696])).
% 3.44/1.68  tff(c_1767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1734, c_1751])).
% 3.44/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.68  
% 3.44/1.68  Inference rules
% 3.44/1.68  ----------------------
% 3.44/1.68  #Ref     : 0
% 3.44/1.68  #Sup     : 424
% 3.44/1.68  #Fact    : 0
% 3.44/1.68  #Define  : 0
% 3.44/1.68  #Split   : 0
% 3.44/1.68  #Chain   : 0
% 3.44/1.68  #Close   : 0
% 3.44/1.68  
% 3.44/1.68  Ordering : KBO
% 3.44/1.68  
% 3.44/1.68  Simplification rules
% 3.44/1.68  ----------------------
% 3.44/1.68  #Subsume      : 8
% 3.44/1.68  #Demod        : 244
% 3.44/1.68  #Tautology    : 278
% 3.44/1.68  #SimpNegUnit  : 0
% 3.44/1.68  #BackRed      : 31
% 3.44/1.68  
% 3.44/1.68  #Partial instantiations: 0
% 3.44/1.68  #Strategies tried      : 1
% 3.44/1.68  
% 3.44/1.68  Timing (in seconds)
% 3.44/1.68  ----------------------
% 3.44/1.68  Preprocessing        : 0.31
% 3.44/1.68  Parsing              : 0.16
% 3.44/1.68  CNF conversion       : 0.02
% 3.44/1.68  Main loop            : 0.46
% 3.44/1.68  Inferencing          : 0.15
% 3.44/1.68  Reduction            : 0.18
% 3.44/1.68  Demodulation         : 0.15
% 3.44/1.68  BG Simplification    : 0.03
% 3.44/1.68  Subsumption          : 0.06
% 3.44/1.68  Abstraction          : 0.03
% 3.44/1.68  MUC search           : 0.00
% 3.44/1.68  Cooper               : 0.00
% 3.44/1.68  Total                : 0.80
% 3.44/1.68  Index Insertion      : 0.00
% 3.44/1.68  Index Deletion       : 0.00
% 3.44/1.68  Index Matching       : 0.00
% 3.44/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
