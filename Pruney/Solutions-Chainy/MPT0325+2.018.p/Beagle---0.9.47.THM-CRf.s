%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 29.96s
% Output     : CNFRefutation 30.20s
% Verified   : 
% Statistics : Number of formulae       :  177 (1193 expanded)
%              Number of leaves         :   24 ( 405 expanded)
%              Depth                    :   16
%              Number of atoms          :  232 (1810 expanded)
%              Number of equality atoms :  150 (1361 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(c_86581,plain,(
    ! [A_900,B_901] :
      ( r1_tarski(A_900,B_901)
      | k4_xboole_0(A_900,B_901) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_106])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_130])).

tff(c_148,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_145])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_964,plain,(
    ! [A_86,C_87,B_88,D_89] : k3_xboole_0(k2_zfmisc_1(A_86,C_87),k2_zfmisc_1(B_88,D_89)) = k2_zfmisc_1(k3_xboole_0(A_86,B_88),k3_xboole_0(C_87,D_89)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_982,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_111])).

tff(c_1059,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_982])).

tff(c_2588,plain,(
    ! [B_140,D_141,A_142,C_143] : k3_xboole_0(k2_zfmisc_1(B_140,D_141),k2_zfmisc_1(A_142,C_143)) = k2_zfmisc_1(k3_xboole_0(A_142,B_140),k3_xboole_0(C_143,D_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_2])).

tff(c_156,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k3_xboole_0(A_39,C_40),B_41)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,(
    ! [A_39,C_40,B_41] :
      ( k4_xboole_0(k3_xboole_0(A_39,C_40),B_41) = k1_xboole_0
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_25828,plain,(
    ! [C_467,B_466,B_469,D_465,A_468] :
      ( k4_xboole_0(k2_zfmisc_1(k3_xboole_0(A_468,B_466),k3_xboole_0(C_467,D_465)),B_469) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(B_466,D_465),B_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_172])).

tff(c_26331,plain,(
    ! [B_470] :
      ( k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),B_470) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1059,c_25828])).

tff(c_84973,plain,(
    ! [B_884] :
      ( k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),B_884) = k1_xboole_0
      | k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'),B_884) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_26331])).

tff(c_85043,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_84973])).

tff(c_26,plain,(
    ! [A_21,C_23,B_22] : k4_xboole_0(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,C_23)) = k2_zfmisc_1(k4_xboole_0(A_21,B_22),C_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85176,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85043,c_26])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85357,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85176,c_18])).

tff(c_85406,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_85357])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k3_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_321,plain,(
    ! [C_57,A_58,B_59] : k4_xboole_0(k2_zfmisc_1(C_57,A_58),k2_zfmisc_1(C_57,B_59)) = k2_zfmisc_1(C_57,k4_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_350,plain,(
    ! [A_15,A_58] : k4_xboole_0(k2_zfmisc_1(A_15,A_58),k1_xboole_0) = k2_zfmisc_1(A_15,k4_xboole_0(A_58,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_586,plain,(
    ! [A_71,C_72,B_73] : k4_xboole_0(k2_zfmisc_1(A_71,C_72),k2_zfmisc_1(B_73,C_72)) = k2_zfmisc_1(k4_xboole_0(A_71,B_73),C_72) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_617,plain,(
    ! [A_71,B_16] : k4_xboole_0(k2_zfmisc_1(A_71,B_16),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0(A_71,k1_xboole_0),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_586])).

tff(c_686,plain,(
    ! [A_76,B_77] : k2_zfmisc_1(k4_xboole_0(A_76,k1_xboole_0),B_77) = k2_zfmisc_1(A_76,k4_xboole_0(B_77,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_617])).

tff(c_736,plain,(
    ! [A_39,C_40,B_77] :
      ( k2_zfmisc_1(k3_xboole_0(A_39,C_40),k4_xboole_0(B_77,k1_xboole_0)) = k2_zfmisc_1(k1_xboole_0,B_77)
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_686])).

tff(c_1551,plain,(
    ! [A_109,C_110,B_111] :
      ( k2_zfmisc_1(k3_xboole_0(A_109,C_110),k4_xboole_0(B_111,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(A_109,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_736])).

tff(c_1652,plain,(
    ! [A_112,B_113] :
      ( k2_zfmisc_1(A_112,k4_xboole_0(B_113,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1551])).

tff(c_1749,plain,(
    ! [B_113,A_112] :
      ( k4_xboole_0(B_113,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_18])).

tff(c_1879,plain,(
    ! [A_117] :
      ( k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_1749])).

tff(c_1980,plain,(
    ! [A_121,C_122] :
      ( k3_xboole_0(A_121,C_122) = k1_xboole_0
      | ~ r1_tarski(A_121,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1879])).

tff(c_2022,plain,(
    ! [A_125,C_126] :
      ( k3_xboole_0(A_125,C_126) = k1_xboole_0
      | k4_xboole_0(A_125,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1980])).

tff(c_2180,plain,(
    ! [C_130] : k3_xboole_0(k1_xboole_0,C_130) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2022])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2225,plain,(
    ! [C_130] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_10])).

tff(c_2261,plain,(
    ! [C_130] : k4_xboole_0(k1_xboole_0,C_130) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2225])).

tff(c_168,plain,(
    ! [A_1,B_2,B_41] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_41)
      | ~ r1_tarski(B_2,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_2462,plain,(
    ! [B_134,C_135] :
      ( r1_tarski(k1_xboole_0,B_134)
      | ~ r1_tarski(C_135,B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_168])).

tff(c_2527,plain,(
    ! [B_137,A_138] :
      ( r1_tarski(k1_xboole_0,B_137)
      | k4_xboole_0(A_138,B_137) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2462])).

tff(c_2544,plain,(
    ! [C_130] : r1_tarski(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_2261,c_2527])).

tff(c_85592,plain,(
    ! [C_130] : r1_tarski('#skF_2',C_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85406,c_2544])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_185,plain,(
    ! [A_44,B_45,B_46] :
      ( r1_tarski(k3_xboole_0(A_44,B_45),B_46)
      | ~ r1_tarski(B_45,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_201,plain,(
    ! [A_44,B_45,B_46] :
      ( k4_xboole_0(k3_xboole_0(A_44,B_45),B_46) = k1_xboole_0
      | ~ r1_tarski(B_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_185,c_8])).

tff(c_1905,plain,(
    ! [A_118] :
      ( k1_xboole_0 = A_118
      | k4_xboole_0(A_118,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1879])).

tff(c_4651,plain,(
    ! [A_196,A_197] :
      ( k2_zfmisc_1(A_196,A_197) = k1_xboole_0
      | k2_zfmisc_1(A_196,k4_xboole_0(A_197,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1905])).

tff(c_4680,plain,(
    ! [A_196,A_44,B_45] :
      ( k2_zfmisc_1(A_196,k3_xboole_0(A_44,B_45)) = k1_xboole_0
      | k2_zfmisc_1(A_196,k1_xboole_0) != k1_xboole_0
      | ~ r1_tarski(B_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4651])).

tff(c_5287,plain,(
    ! [A_216,A_217,B_218] :
      ( k2_zfmisc_1(A_216,k3_xboole_0(A_217,B_218)) = k1_xboole_0
      | ~ r1_tarski(B_218,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4680])).

tff(c_5323,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_1059])).

tff(c_5434,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5323])).

tff(c_85558,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85406,c_5434])).

tff(c_86117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85592,c_85558])).

tff(c_86127,plain,(
    ! [B_890] : k4_xboole_0(B_890,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1749])).

tff(c_428,plain,(
    ! [A_65,C_66,B_67] :
      ( k3_xboole_0(k3_xboole_0(A_65,C_66),B_67) = k3_xboole_0(A_65,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_764,plain,(
    ! [B_79,A_80,C_81] :
      ( k3_xboole_0(B_79,k3_xboole_0(A_80,C_81)) = k3_xboole_0(A_80,C_81)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_2])).

tff(c_852,plain,(
    ! [B_79,A_3] :
      ( k3_xboole_0(B_79,A_3) = k3_xboole_0(A_3,A_3)
      | ~ r1_tarski(A_3,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_764])).

tff(c_864,plain,(
    ! [B_82,A_83] :
      ( k3_xboole_0(B_82,A_83) = A_83
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_852])).

tff(c_879,plain,(
    ! [B_6,A_5] :
      ( k3_xboole_0(B_6,A_5) = A_5
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_864])).

tff(c_86165,plain,(
    ! [B_890] : k3_xboole_0(k1_xboole_0,B_890) = B_890 ),
    inference(superposition,[status(thm),theory(equality)],[c_86127,c_879])).

tff(c_128,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_14])).

tff(c_86169,plain,(
    ! [B_890] : k3_xboole_0(B_890,k1_xboole_0) = B_890 ),
    inference(superposition,[status(thm),theory(equality)],[c_86127,c_128])).

tff(c_1043,plain,(
    ! [A_86,C_87,B_16] : k2_zfmisc_1(k3_xboole_0(A_86,k1_xboole_0),k3_xboole_0(C_87,B_16)) = k3_xboole_0(k2_zfmisc_1(A_86,C_87),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_964])).

tff(c_1068,plain,(
    ! [A_86,C_87,B_16] : k2_zfmisc_1(k3_xboole_0(A_86,k1_xboole_0),k3_xboole_0(C_87,B_16)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_86,C_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1043])).

tff(c_86438,plain,(
    ! [A_895,C_896,B_897] : k2_zfmisc_1(A_895,k3_xboole_0(C_896,B_897)) = k2_zfmisc_1(A_895,C_896) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86169,c_86165,c_1068])).

tff(c_86479,plain,(
    ! [A_895,B_890] : k2_zfmisc_1(A_895,k1_xboole_0) = k2_zfmisc_1(A_895,B_890) ),
    inference(superposition,[status(thm),theory(equality)],[c_86165,c_86438])).

tff(c_86528,plain,(
    ! [A_895,B_890] : k2_zfmisc_1(A_895,B_890) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_86479])).

tff(c_86565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86528,c_32])).

tff(c_86566,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_86589,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86581,c_86566])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] : k4_xboole_0(k2_zfmisc_1(C_23,A_21),k2_zfmisc_1(C_23,B_22)) = k2_zfmisc_1(C_23,k4_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87134,plain,(
    ! [A_944,C_945,B_946,D_947] : k3_xboole_0(k2_zfmisc_1(A_944,C_945),k2_zfmisc_1(B_946,D_947)) = k2_zfmisc_1(k3_xboole_0(A_944,B_946),k3_xboole_0(C_945,D_947)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90498,plain,(
    ! [A_1421,C_1422,B_1423,D_1424] : k5_xboole_0(k2_zfmisc_1(A_1421,C_1422),k2_zfmisc_1(k3_xboole_0(A_1421,B_1423),k3_xboole_0(C_1422,D_1424))) = k4_xboole_0(k2_zfmisc_1(A_1421,C_1422),k2_zfmisc_1(B_1423,D_1424)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87134,c_10])).

tff(c_90588,plain,(
    ! [A_3,C_1422,D_1424] : k5_xboole_0(k2_zfmisc_1(A_3,C_1422),k2_zfmisc_1(A_3,k3_xboole_0(C_1422,D_1424))) = k4_xboole_0(k2_zfmisc_1(A_3,C_1422),k2_zfmisc_1(A_3,D_1424)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_90498])).

tff(c_90604,plain,(
    ! [A_3,C_1422,D_1424] : k5_xboole_0(k2_zfmisc_1(A_3,C_1422),k2_zfmisc_1(A_3,k3_xboole_0(C_1422,D_1424))) = k2_zfmisc_1(A_3,k4_xboole_0(C_1422,D_1424)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_90588])).

tff(c_86567,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_86590,plain,(
    ! [A_902,B_903] :
      ( k3_xboole_0(A_902,B_903) = A_902
      | ~ r1_tarski(A_902,B_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86601,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_86567,c_86590])).

tff(c_90567,plain,(
    ! [C_1422,D_1424] : k5_xboole_0(k2_zfmisc_1('#skF_1',C_1422),k2_zfmisc_1('#skF_1',k3_xboole_0(C_1422,D_1424))) = k4_xboole_0(k2_zfmisc_1('#skF_1',C_1422),k2_zfmisc_1('#skF_3',D_1424)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86601,c_90498])).

tff(c_133446,plain,(
    ! [C_1955,D_1956] : k4_xboole_0(k2_zfmisc_1('#skF_1',C_1955),k2_zfmisc_1('#skF_3',D_1956)) = k2_zfmisc_1('#skF_1',k4_xboole_0(C_1955,D_1956)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90604,c_90567])).

tff(c_86568,plain,(
    ! [A_898,B_899] :
      ( k4_xboole_0(A_898,B_899) = k1_xboole_0
      | ~ r1_tarski(A_898,B_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86576,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_86568])).

tff(c_133530,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133446,c_86576])).

tff(c_133822,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_133530,c_18])).

tff(c_133862,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86589,c_133822])).

tff(c_86643,plain,(
    ! [A_909,B_910] : k5_xboole_0(A_909,k3_xboole_0(A_909,B_910)) = k4_xboole_0(A_909,B_910) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86661,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_86643])).

tff(c_86665,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_86661])).

tff(c_87507,plain,(
    ! [A_957,B_958,D_959] : k2_zfmisc_1(k3_xboole_0(A_957,B_958),k3_xboole_0(k1_xboole_0,D_959)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_958,D_959)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_87134])).

tff(c_87579,plain,(
    ! [A_3,D_959] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_3,D_959)) = k2_zfmisc_1(A_3,k3_xboole_0(k1_xboole_0,D_959)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87507])).

tff(c_87198,plain,(
    ! [A_944,C_945,B_16] : k2_zfmisc_1(k3_xboole_0(A_944,k1_xboole_0),k3_xboole_0(C_945,B_16)) = k3_xboole_0(k2_zfmisc_1(A_944,C_945),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_87134])).

tff(c_87218,plain,(
    ! [A_944,C_945,B_16] : k2_zfmisc_1(k3_xboole_0(A_944,k1_xboole_0),k3_xboole_0(C_945,B_16)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_944,C_945)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_87198])).

tff(c_88267,plain,(
    ! [A_944,C_945,B_16] : k2_zfmisc_1(k3_xboole_0(A_944,k1_xboole_0),k3_xboole_0(C_945,B_16)) = k2_zfmisc_1(A_944,k3_xboole_0(k1_xboole_0,C_945)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87579,c_87218])).

tff(c_88268,plain,(
    ! [A_979,C_980,B_981] : k2_zfmisc_1(k3_xboole_0(A_979,k1_xboole_0),k3_xboole_0(C_980,B_981)) = k2_zfmisc_1(A_979,k3_xboole_0(k1_xboole_0,C_980)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87579,c_87218])).

tff(c_88278,plain,(
    ! [A_979,C_980,B_981] : k2_zfmisc_1(k3_xboole_0(A_979,k1_xboole_0),k3_xboole_0(k1_xboole_0,k3_xboole_0(C_980,B_981))) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_979,k3_xboole_0(k1_xboole_0,C_980))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88268,c_87579])).

tff(c_88384,plain,(
    ! [A_982,C_983] : k2_zfmisc_1(A_982,k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_983))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_88267,c_87579,c_88278])).

tff(c_88507,plain,(
    ! [C_983,A_982] :
      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_983)) = k1_xboole_0
      | k1_xboole_0 = A_982 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88384,c_18])).

tff(c_88518,plain,(
    ! [A_984] : k1_xboole_0 = A_984 ),
    inference(splitLeft,[status(thm)],[c_88507])).

tff(c_86607,plain,(
    ! [A_904,C_905,B_906] :
      ( r1_tarski(k3_xboole_0(A_904,C_905),B_906)
      | ~ r1_tarski(A_904,B_906) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87271,plain,(
    ! [A_950,C_951,B_952] :
      ( k3_xboole_0(k3_xboole_0(A_950,C_951),B_952) = k3_xboole_0(A_950,C_951)
      | ~ r1_tarski(A_950,B_952) ) ),
    inference(resolution,[status(thm)],[c_86607,c_14])).

tff(c_87351,plain,(
    ! [A_953,A_954,C_955] :
      ( k3_xboole_0(A_953,k3_xboole_0(A_954,C_955)) = k3_xboole_0(A_954,C_955)
      | ~ r1_tarski(A_954,A_953) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87271])).

tff(c_87431,plain,(
    ! [A_953,A_3] :
      ( k3_xboole_0(A_953,A_3) = k3_xboole_0(A_3,A_3)
      | ~ r1_tarski(A_3,A_953) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87351])).

tff(c_87589,plain,(
    ! [A_960,A_961] :
      ( k3_xboole_0(A_960,A_961) = A_961
      | ~ r1_tarski(A_961,A_960) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87431])).

tff(c_87614,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_87589])).

tff(c_88688,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88518,c_87614])).

tff(c_88860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_88688])).

tff(c_88935,plain,(
    ! [C_1389] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_1389)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88507])).

tff(c_87334,plain,(
    ! [A_1,A_950,C_951] :
      ( k3_xboole_0(A_1,k3_xboole_0(A_950,C_951)) = k3_xboole_0(A_950,C_951)
      | ~ r1_tarski(A_950,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87271])).

tff(c_88957,plain,(
    ! [C_1389] :
      ( k3_xboole_0(k1_xboole_0,C_1389) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88935,c_87334])).

tff(c_89675,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_88957])).

tff(c_89678,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_89675])).

tff(c_89682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86665,c_89678])).

tff(c_89907,plain,(
    ! [C_1403] : k3_xboole_0(k1_xboole_0,C_1403) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88957])).

tff(c_89944,plain,(
    ! [C_1403] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,C_1403) ),
    inference(superposition,[status(thm),theory(equality)],[c_89907,c_10])).

tff(c_89982,plain,(
    ! [C_1403] : k4_xboole_0(k1_xboole_0,C_1403) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_89944])).

tff(c_86619,plain,(
    ! [B_2,A_1,B_906] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_906)
      | ~ r1_tarski(A_1,B_906) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86607])).

tff(c_90283,plain,(
    ! [B_1412,C_1413] :
      ( r1_tarski(k1_xboole_0,B_1412)
      | ~ r1_tarski(C_1413,B_1412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89907,c_86619])).

tff(c_90425,plain,(
    ! [B_1418,A_1419] :
      ( r1_tarski(k1_xboole_0,B_1418)
      | k4_xboole_0(A_1419,B_1418) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_90283])).

tff(c_90444,plain,(
    ! [C_1403] : r1_tarski(k1_xboole_0,C_1403) ),
    inference(superposition,[status(thm),theory(equality)],[c_89982,c_90425])).

tff(c_134013,plain,(
    ! [C_1403] : r1_tarski('#skF_1',C_1403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133862,c_90444])).

tff(c_86627,plain,(
    ! [A_904,C_905,B_906] :
      ( k4_xboole_0(k3_xboole_0(A_904,C_905),B_906) = k1_xboole_0
      | ~ r1_tarski(A_904,B_906) ) ),
    inference(resolution,[status(thm)],[c_86607,c_8])).

tff(c_86726,plain,(
    ! [C_916,A_917,B_918] : k4_xboole_0(k2_zfmisc_1(C_916,A_917),k2_zfmisc_1(C_916,B_918)) = k2_zfmisc_1(C_916,k4_xboole_0(A_917,B_918)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86755,plain,(
    ! [A_15,A_917] : k4_xboole_0(k2_zfmisc_1(A_15,A_917),k1_xboole_0) = k2_zfmisc_1(A_15,k4_xboole_0(A_917,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_86726])).

tff(c_86868,plain,(
    ! [A_929,C_930,B_931] : k4_xboole_0(k2_zfmisc_1(A_929,C_930),k2_zfmisc_1(B_931,C_930)) = k2_zfmisc_1(k4_xboole_0(A_929,B_931),C_930) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86899,plain,(
    ! [A_929,B_16] : k4_xboole_0(k2_zfmisc_1(A_929,B_16),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0(A_929,k1_xboole_0),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_86868])).

tff(c_87062,plain,(
    ! [A_942,B_943] : k2_zfmisc_1(k4_xboole_0(A_942,k1_xboole_0),B_943) = k2_zfmisc_1(A_942,k4_xboole_0(B_943,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86755,c_86899])).

tff(c_87112,plain,(
    ! [A_904,C_905,B_943] :
      ( k2_zfmisc_1(k3_xboole_0(A_904,C_905),k4_xboole_0(B_943,k1_xboole_0)) = k2_zfmisc_1(k1_xboole_0,B_943)
      | ~ r1_tarski(A_904,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86627,c_87062])).

tff(c_90617,plain,(
    ! [A_1425,C_1426,B_1427] :
      ( k2_zfmisc_1(k3_xboole_0(A_1425,C_1426),k4_xboole_0(B_1427,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(A_1425,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_87112])).

tff(c_90702,plain,(
    ! [B_1427] :
      ( k2_zfmisc_1('#skF_1',k4_xboole_0(B_1427,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski('#skF_1',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86601,c_90617])).

tff(c_91043,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_90702])).

tff(c_134004,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133862,c_91043])).

tff(c_134052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134013,c_134004])).

tff(c_134054,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_90702])).

tff(c_87443,plain,(
    ! [A_953,A_3] :
      ( k3_xboole_0(A_953,A_3) = A_3
      | ~ r1_tarski(A_3,A_953) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87431])).

tff(c_134070,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_134054,c_87443])).

tff(c_89683,plain,(
    ! [C_1389] : k3_xboole_0(k1_xboole_0,C_1389) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88957])).

tff(c_134096,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_134070,c_89683])).

tff(c_134195,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_1',B_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134096,c_134096,c_22])).

tff(c_134198,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134096,c_32])).

tff(c_134422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134195,c_134198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.96/18.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.96/18.53  
% 29.96/18.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.96/18.53  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 29.96/18.53  
% 29.96/18.53  %Foreground sorts:
% 29.96/18.53  
% 29.96/18.53  
% 29.96/18.53  %Background operators:
% 29.96/18.53  
% 29.96/18.53  
% 29.96/18.53  %Foreground operators:
% 29.96/18.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.96/18.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.96/18.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.96/18.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.96/18.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.96/18.53  tff('#skF_2', type, '#skF_2': $i).
% 29.96/18.53  tff('#skF_3', type, '#skF_3': $i).
% 29.96/18.53  tff('#skF_1', type, '#skF_1': $i).
% 29.96/18.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.96/18.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.96/18.53  tff('#skF_4', type, '#skF_4': $i).
% 29.96/18.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.96/18.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.96/18.53  
% 30.20/18.56  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 30.20/18.56  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 30.20/18.56  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 30.20/18.56  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 30.20/18.56  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 30.20/18.56  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 30.20/18.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 30.20/18.56  tff(f_53, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 30.20/18.56  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 30.20/18.56  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 30.20/18.56  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 30.20/18.56  tff(c_86581, plain, (![A_900, B_901]: (r1_tarski(A_900, B_901) | k4_xboole_0(A_900, B_901)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.20/18.56  tff(c_20, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.20/18.56  tff(c_117, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.20/18.56  tff(c_30, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 30.20/18.56  tff(c_106, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 30.20/18.56  tff(c_129, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_117, c_106])).
% 30.20/18.56  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.20/18.56  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 30.20/18.56  tff(c_130, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.20/18.56  tff(c_145, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_130])).
% 30.20/18.56  tff(c_148, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_145])).
% 30.20/18.56  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.20/18.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.20/18.56  tff(c_964, plain, (![A_86, C_87, B_88, D_89]: (k3_xboole_0(k2_zfmisc_1(A_86, C_87), k2_zfmisc_1(B_88, D_89))=k2_zfmisc_1(k3_xboole_0(A_86, B_88), k3_xboole_0(C_87, D_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 30.20/18.56  tff(c_34, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 30.20/18.56  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.20/18.56  tff(c_111, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_14])).
% 30.20/18.56  tff(c_982, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_964, c_111])).
% 30.20/18.56  tff(c_1059, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_982])).
% 30.20/18.56  tff(c_2588, plain, (![B_140, D_141, A_142, C_143]: (k3_xboole_0(k2_zfmisc_1(B_140, D_141), k2_zfmisc_1(A_142, C_143))=k2_zfmisc_1(k3_xboole_0(A_142, B_140), k3_xboole_0(C_143, D_141)))), inference(superposition, [status(thm), theory('equality')], [c_964, c_2])).
% 30.20/18.56  tff(c_156, plain, (![A_39, C_40, B_41]: (r1_tarski(k3_xboole_0(A_39, C_40), B_41) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.20/18.56  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.20/18.56  tff(c_172, plain, (![A_39, C_40, B_41]: (k4_xboole_0(k3_xboole_0(A_39, C_40), B_41)=k1_xboole_0 | ~r1_tarski(A_39, B_41))), inference(resolution, [status(thm)], [c_156, c_8])).
% 30.20/18.56  tff(c_25828, plain, (![C_467, B_466, B_469, D_465, A_468]: (k4_xboole_0(k2_zfmisc_1(k3_xboole_0(A_468, B_466), k3_xboole_0(C_467, D_465)), B_469)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(B_466, D_465), B_469))), inference(superposition, [status(thm), theory('equality')], [c_2588, c_172])).
% 30.20/18.56  tff(c_26331, plain, (![B_470]: (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), B_470)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_470))), inference(superposition, [status(thm), theory('equality')], [c_1059, c_25828])).
% 30.20/18.56  tff(c_84973, plain, (![B_884]: (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), B_884)=k1_xboole_0 | k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'), B_884)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_26331])).
% 30.20/18.56  tff(c_85043, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_148, c_84973])).
% 30.20/18.56  tff(c_26, plain, (![A_21, C_23, B_22]: (k4_xboole_0(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, C_23))=k2_zfmisc_1(k4_xboole_0(A_21, B_22), C_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_85176, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_85043, c_26])).
% 30.20/18.56  tff(c_18, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.20/18.56  tff(c_85357, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_85176, c_18])).
% 30.20/18.56  tff(c_85406, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_129, c_85357])).
% 30.20/18.56  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(k3_xboole_0(A_9, C_11), B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.20/18.56  tff(c_22, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.20/18.56  tff(c_321, plain, (![C_57, A_58, B_59]: (k4_xboole_0(k2_zfmisc_1(C_57, A_58), k2_zfmisc_1(C_57, B_59))=k2_zfmisc_1(C_57, k4_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_350, plain, (![A_15, A_58]: (k4_xboole_0(k2_zfmisc_1(A_15, A_58), k1_xboole_0)=k2_zfmisc_1(A_15, k4_xboole_0(A_58, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_321])).
% 30.20/18.56  tff(c_586, plain, (![A_71, C_72, B_73]: (k4_xboole_0(k2_zfmisc_1(A_71, C_72), k2_zfmisc_1(B_73, C_72))=k2_zfmisc_1(k4_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_617, plain, (![A_71, B_16]: (k4_xboole_0(k2_zfmisc_1(A_71, B_16), k1_xboole_0)=k2_zfmisc_1(k4_xboole_0(A_71, k1_xboole_0), B_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_586])).
% 30.20/18.56  tff(c_686, plain, (![A_76, B_77]: (k2_zfmisc_1(k4_xboole_0(A_76, k1_xboole_0), B_77)=k2_zfmisc_1(A_76, k4_xboole_0(B_77, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_617])).
% 30.20/18.56  tff(c_736, plain, (![A_39, C_40, B_77]: (k2_zfmisc_1(k3_xboole_0(A_39, C_40), k4_xboole_0(B_77, k1_xboole_0))=k2_zfmisc_1(k1_xboole_0, B_77) | ~r1_tarski(A_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_686])).
% 30.20/18.56  tff(c_1551, plain, (![A_109, C_110, B_111]: (k2_zfmisc_1(k3_xboole_0(A_109, C_110), k4_xboole_0(B_111, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(A_109, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_736])).
% 30.20/18.56  tff(c_1652, plain, (![A_112, B_113]: (k2_zfmisc_1(A_112, k4_xboole_0(B_113, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1551])).
% 30.20/18.56  tff(c_1749, plain, (![B_113, A_112]: (k4_xboole_0(B_113, k1_xboole_0)=k1_xboole_0 | k1_xboole_0=A_112 | ~r1_tarski(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1652, c_18])).
% 30.20/18.56  tff(c_1879, plain, (![A_117]: (k1_xboole_0=A_117 | ~r1_tarski(A_117, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1749])).
% 30.20/18.56  tff(c_1980, plain, (![A_121, C_122]: (k3_xboole_0(A_121, C_122)=k1_xboole_0 | ~r1_tarski(A_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1879])).
% 30.20/18.56  tff(c_2022, plain, (![A_125, C_126]: (k3_xboole_0(A_125, C_126)=k1_xboole_0 | k4_xboole_0(A_125, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1980])).
% 30.20/18.56  tff(c_2180, plain, (![C_130]: (k3_xboole_0(k1_xboole_0, C_130)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_2022])).
% 30.20/18.56  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.20/18.56  tff(c_2225, plain, (![C_130]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_2180, c_10])).
% 30.20/18.56  tff(c_2261, plain, (![C_130]: (k4_xboole_0(k1_xboole_0, C_130)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2225])).
% 30.20/18.56  tff(c_168, plain, (![A_1, B_2, B_41]: (r1_tarski(k3_xboole_0(A_1, B_2), B_41) | ~r1_tarski(B_2, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 30.20/18.56  tff(c_2462, plain, (![B_134, C_135]: (r1_tarski(k1_xboole_0, B_134) | ~r1_tarski(C_135, B_134))), inference(superposition, [status(thm), theory('equality')], [c_2180, c_168])).
% 30.20/18.56  tff(c_2527, plain, (![B_137, A_138]: (r1_tarski(k1_xboole_0, B_137) | k4_xboole_0(A_138, B_137)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2462])).
% 30.20/18.56  tff(c_2544, plain, (![C_130]: (r1_tarski(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_2261, c_2527])).
% 30.20/18.56  tff(c_85592, plain, (![C_130]: (r1_tarski('#skF_2', C_130))), inference(demodulation, [status(thm), theory('equality')], [c_85406, c_2544])).
% 30.20/18.56  tff(c_32, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 30.20/18.56  tff(c_185, plain, (![A_44, B_45, B_46]: (r1_tarski(k3_xboole_0(A_44, B_45), B_46) | ~r1_tarski(B_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 30.20/18.56  tff(c_201, plain, (![A_44, B_45, B_46]: (k4_xboole_0(k3_xboole_0(A_44, B_45), B_46)=k1_xboole_0 | ~r1_tarski(B_45, B_46))), inference(resolution, [status(thm)], [c_185, c_8])).
% 30.20/18.56  tff(c_1905, plain, (![A_118]: (k1_xboole_0=A_118 | k4_xboole_0(A_118, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1879])).
% 30.20/18.56  tff(c_4651, plain, (![A_196, A_197]: (k2_zfmisc_1(A_196, A_197)=k1_xboole_0 | k2_zfmisc_1(A_196, k4_xboole_0(A_197, k1_xboole_0))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_350, c_1905])).
% 30.20/18.56  tff(c_4680, plain, (![A_196, A_44, B_45]: (k2_zfmisc_1(A_196, k3_xboole_0(A_44, B_45))=k1_xboole_0 | k2_zfmisc_1(A_196, k1_xboole_0)!=k1_xboole_0 | ~r1_tarski(B_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201, c_4651])).
% 30.20/18.56  tff(c_5287, plain, (![A_216, A_217, B_218]: (k2_zfmisc_1(A_216, k3_xboole_0(A_217, B_218))=k1_xboole_0 | ~r1_tarski(B_218, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4680])).
% 30.20/18.56  tff(c_5323, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5287, c_1059])).
% 30.20/18.56  tff(c_5434, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_32, c_5323])).
% 30.20/18.56  tff(c_85558, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85406, c_5434])).
% 30.20/18.56  tff(c_86117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85592, c_85558])).
% 30.20/18.56  tff(c_86127, plain, (![B_890]: (k4_xboole_0(B_890, k1_xboole_0)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_1749])).
% 30.20/18.56  tff(c_428, plain, (![A_65, C_66, B_67]: (k3_xboole_0(k3_xboole_0(A_65, C_66), B_67)=k3_xboole_0(A_65, C_66) | ~r1_tarski(A_65, B_67))), inference(resolution, [status(thm)], [c_156, c_14])).
% 30.20/18.56  tff(c_764, plain, (![B_79, A_80, C_81]: (k3_xboole_0(B_79, k3_xboole_0(A_80, C_81))=k3_xboole_0(A_80, C_81) | ~r1_tarski(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_428, c_2])).
% 30.20/18.56  tff(c_852, plain, (![B_79, A_3]: (k3_xboole_0(B_79, A_3)=k3_xboole_0(A_3, A_3) | ~r1_tarski(A_3, B_79))), inference(superposition, [status(thm), theory('equality')], [c_4, c_764])).
% 30.20/18.56  tff(c_864, plain, (![B_82, A_83]: (k3_xboole_0(B_82, A_83)=A_83 | ~r1_tarski(A_83, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_852])).
% 30.20/18.56  tff(c_879, plain, (![B_6, A_5]: (k3_xboole_0(B_6, A_5)=A_5 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_864])).
% 30.20/18.56  tff(c_86165, plain, (![B_890]: (k3_xboole_0(k1_xboole_0, B_890)=B_890)), inference(superposition, [status(thm), theory('equality')], [c_86127, c_879])).
% 30.20/18.56  tff(c_128, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_14])).
% 30.20/18.56  tff(c_86169, plain, (![B_890]: (k3_xboole_0(B_890, k1_xboole_0)=B_890)), inference(superposition, [status(thm), theory('equality')], [c_86127, c_128])).
% 30.20/18.56  tff(c_1043, plain, (![A_86, C_87, B_16]: (k2_zfmisc_1(k3_xboole_0(A_86, k1_xboole_0), k3_xboole_0(C_87, B_16))=k3_xboole_0(k2_zfmisc_1(A_86, C_87), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_964])).
% 30.20/18.56  tff(c_1068, plain, (![A_86, C_87, B_16]: (k2_zfmisc_1(k3_xboole_0(A_86, k1_xboole_0), k3_xboole_0(C_87, B_16))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_86, C_87)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1043])).
% 30.20/18.56  tff(c_86438, plain, (![A_895, C_896, B_897]: (k2_zfmisc_1(A_895, k3_xboole_0(C_896, B_897))=k2_zfmisc_1(A_895, C_896))), inference(demodulation, [status(thm), theory('equality')], [c_86169, c_86165, c_1068])).
% 30.20/18.56  tff(c_86479, plain, (![A_895, B_890]: (k2_zfmisc_1(A_895, k1_xboole_0)=k2_zfmisc_1(A_895, B_890))), inference(superposition, [status(thm), theory('equality')], [c_86165, c_86438])).
% 30.20/18.56  tff(c_86528, plain, (![A_895, B_890]: (k2_zfmisc_1(A_895, B_890)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_86479])).
% 30.20/18.56  tff(c_86565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86528, c_32])).
% 30.20/18.56  tff(c_86566, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 30.20/18.56  tff(c_86589, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86581, c_86566])).
% 30.20/18.56  tff(c_28, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k2_zfmisc_1(C_23, A_21), k2_zfmisc_1(C_23, B_22))=k2_zfmisc_1(C_23, k4_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_87134, plain, (![A_944, C_945, B_946, D_947]: (k3_xboole_0(k2_zfmisc_1(A_944, C_945), k2_zfmisc_1(B_946, D_947))=k2_zfmisc_1(k3_xboole_0(A_944, B_946), k3_xboole_0(C_945, D_947)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 30.20/18.56  tff(c_90498, plain, (![A_1421, C_1422, B_1423, D_1424]: (k5_xboole_0(k2_zfmisc_1(A_1421, C_1422), k2_zfmisc_1(k3_xboole_0(A_1421, B_1423), k3_xboole_0(C_1422, D_1424)))=k4_xboole_0(k2_zfmisc_1(A_1421, C_1422), k2_zfmisc_1(B_1423, D_1424)))), inference(superposition, [status(thm), theory('equality')], [c_87134, c_10])).
% 30.20/18.56  tff(c_90588, plain, (![A_3, C_1422, D_1424]: (k5_xboole_0(k2_zfmisc_1(A_3, C_1422), k2_zfmisc_1(A_3, k3_xboole_0(C_1422, D_1424)))=k4_xboole_0(k2_zfmisc_1(A_3, C_1422), k2_zfmisc_1(A_3, D_1424)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_90498])).
% 30.20/18.56  tff(c_90604, plain, (![A_3, C_1422, D_1424]: (k5_xboole_0(k2_zfmisc_1(A_3, C_1422), k2_zfmisc_1(A_3, k3_xboole_0(C_1422, D_1424)))=k2_zfmisc_1(A_3, k4_xboole_0(C_1422, D_1424)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_90588])).
% 30.20/18.56  tff(c_86567, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 30.20/18.56  tff(c_86590, plain, (![A_902, B_903]: (k3_xboole_0(A_902, B_903)=A_902 | ~r1_tarski(A_902, B_903))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.20/18.56  tff(c_86601, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_86567, c_86590])).
% 30.20/18.56  tff(c_90567, plain, (![C_1422, D_1424]: (k5_xboole_0(k2_zfmisc_1('#skF_1', C_1422), k2_zfmisc_1('#skF_1', k3_xboole_0(C_1422, D_1424)))=k4_xboole_0(k2_zfmisc_1('#skF_1', C_1422), k2_zfmisc_1('#skF_3', D_1424)))), inference(superposition, [status(thm), theory('equality')], [c_86601, c_90498])).
% 30.20/18.56  tff(c_133446, plain, (![C_1955, D_1956]: (k4_xboole_0(k2_zfmisc_1('#skF_1', C_1955), k2_zfmisc_1('#skF_3', D_1956))=k2_zfmisc_1('#skF_1', k4_xboole_0(C_1955, D_1956)))), inference(demodulation, [status(thm), theory('equality')], [c_90604, c_90567])).
% 30.20/18.56  tff(c_86568, plain, (![A_898, B_899]: (k4_xboole_0(A_898, B_899)=k1_xboole_0 | ~r1_tarski(A_898, B_899))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.20/18.56  tff(c_86576, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_86568])).
% 30.20/18.56  tff(c_133530, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_133446, c_86576])).
% 30.20/18.56  tff(c_133822, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_133530, c_18])).
% 30.20/18.56  tff(c_133862, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86589, c_133822])).
% 30.20/18.56  tff(c_86643, plain, (![A_909, B_910]: (k5_xboole_0(A_909, k3_xboole_0(A_909, B_910))=k4_xboole_0(A_909, B_910))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.20/18.56  tff(c_86661, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_86643])).
% 30.20/18.56  tff(c_86665, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_86661])).
% 30.20/18.56  tff(c_87507, plain, (![A_957, B_958, D_959]: (k2_zfmisc_1(k3_xboole_0(A_957, B_958), k3_xboole_0(k1_xboole_0, D_959))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_958, D_959)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_87134])).
% 30.20/18.56  tff(c_87579, plain, (![A_3, D_959]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_3, D_959))=k2_zfmisc_1(A_3, k3_xboole_0(k1_xboole_0, D_959)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87507])).
% 30.20/18.56  tff(c_87198, plain, (![A_944, C_945, B_16]: (k2_zfmisc_1(k3_xboole_0(A_944, k1_xboole_0), k3_xboole_0(C_945, B_16))=k3_xboole_0(k2_zfmisc_1(A_944, C_945), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_87134])).
% 30.20/18.56  tff(c_87218, plain, (![A_944, C_945, B_16]: (k2_zfmisc_1(k3_xboole_0(A_944, k1_xboole_0), k3_xboole_0(C_945, B_16))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_944, C_945)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_87198])).
% 30.20/18.56  tff(c_88267, plain, (![A_944, C_945, B_16]: (k2_zfmisc_1(k3_xboole_0(A_944, k1_xboole_0), k3_xboole_0(C_945, B_16))=k2_zfmisc_1(A_944, k3_xboole_0(k1_xboole_0, C_945)))), inference(demodulation, [status(thm), theory('equality')], [c_87579, c_87218])).
% 30.20/18.56  tff(c_88268, plain, (![A_979, C_980, B_981]: (k2_zfmisc_1(k3_xboole_0(A_979, k1_xboole_0), k3_xboole_0(C_980, B_981))=k2_zfmisc_1(A_979, k3_xboole_0(k1_xboole_0, C_980)))), inference(demodulation, [status(thm), theory('equality')], [c_87579, c_87218])).
% 30.20/18.56  tff(c_88278, plain, (![A_979, C_980, B_981]: (k2_zfmisc_1(k3_xboole_0(A_979, k1_xboole_0), k3_xboole_0(k1_xboole_0, k3_xboole_0(C_980, B_981)))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_979, k3_xboole_0(k1_xboole_0, C_980))))), inference(superposition, [status(thm), theory('equality')], [c_88268, c_87579])).
% 30.20/18.56  tff(c_88384, plain, (![A_982, C_983]: (k2_zfmisc_1(A_982, k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_983)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_88267, c_87579, c_88278])).
% 30.20/18.56  tff(c_88507, plain, (![C_983, A_982]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_983))=k1_xboole_0 | k1_xboole_0=A_982)), inference(superposition, [status(thm), theory('equality')], [c_88384, c_18])).
% 30.20/18.56  tff(c_88518, plain, (![A_984]: (k1_xboole_0=A_984)), inference(splitLeft, [status(thm)], [c_88507])).
% 30.20/18.56  tff(c_86607, plain, (![A_904, C_905, B_906]: (r1_tarski(k3_xboole_0(A_904, C_905), B_906) | ~r1_tarski(A_904, B_906))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.20/18.56  tff(c_87271, plain, (![A_950, C_951, B_952]: (k3_xboole_0(k3_xboole_0(A_950, C_951), B_952)=k3_xboole_0(A_950, C_951) | ~r1_tarski(A_950, B_952))), inference(resolution, [status(thm)], [c_86607, c_14])).
% 30.20/18.56  tff(c_87351, plain, (![A_953, A_954, C_955]: (k3_xboole_0(A_953, k3_xboole_0(A_954, C_955))=k3_xboole_0(A_954, C_955) | ~r1_tarski(A_954, A_953))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87271])).
% 30.20/18.56  tff(c_87431, plain, (![A_953, A_3]: (k3_xboole_0(A_953, A_3)=k3_xboole_0(A_3, A_3) | ~r1_tarski(A_3, A_953))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87351])).
% 30.20/18.56  tff(c_87589, plain, (![A_960, A_961]: (k3_xboole_0(A_960, A_961)=A_961 | ~r1_tarski(A_961, A_960))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87431])).
% 30.20/18.56  tff(c_87614, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_87589])).
% 30.20/18.56  tff(c_88688, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88518, c_87614])).
% 30.20/18.56  tff(c_88860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_88688])).
% 30.20/18.56  tff(c_88935, plain, (![C_1389]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_1389))=k1_xboole_0)), inference(splitRight, [status(thm)], [c_88507])).
% 30.20/18.56  tff(c_87334, plain, (![A_1, A_950, C_951]: (k3_xboole_0(A_1, k3_xboole_0(A_950, C_951))=k3_xboole_0(A_950, C_951) | ~r1_tarski(A_950, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_87271])).
% 30.20/18.56  tff(c_88957, plain, (![C_1389]: (k3_xboole_0(k1_xboole_0, C_1389)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88935, c_87334])).
% 30.20/18.56  tff(c_89675, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_88957])).
% 30.20/18.56  tff(c_89678, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_89675])).
% 30.20/18.56  tff(c_89682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86665, c_89678])).
% 30.20/18.56  tff(c_89907, plain, (![C_1403]: (k3_xboole_0(k1_xboole_0, C_1403)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_88957])).
% 30.20/18.56  tff(c_89944, plain, (![C_1403]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, C_1403))), inference(superposition, [status(thm), theory('equality')], [c_89907, c_10])).
% 30.20/18.56  tff(c_89982, plain, (![C_1403]: (k4_xboole_0(k1_xboole_0, C_1403)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_89944])).
% 30.20/18.56  tff(c_86619, plain, (![B_2, A_1, B_906]: (r1_tarski(k3_xboole_0(B_2, A_1), B_906) | ~r1_tarski(A_1, B_906))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86607])).
% 30.20/18.56  tff(c_90283, plain, (![B_1412, C_1413]: (r1_tarski(k1_xboole_0, B_1412) | ~r1_tarski(C_1413, B_1412))), inference(superposition, [status(thm), theory('equality')], [c_89907, c_86619])).
% 30.20/18.56  tff(c_90425, plain, (![B_1418, A_1419]: (r1_tarski(k1_xboole_0, B_1418) | k4_xboole_0(A_1419, B_1418)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_90283])).
% 30.20/18.56  tff(c_90444, plain, (![C_1403]: (r1_tarski(k1_xboole_0, C_1403))), inference(superposition, [status(thm), theory('equality')], [c_89982, c_90425])).
% 30.20/18.56  tff(c_134013, plain, (![C_1403]: (r1_tarski('#skF_1', C_1403))), inference(demodulation, [status(thm), theory('equality')], [c_133862, c_90444])).
% 30.20/18.56  tff(c_86627, plain, (![A_904, C_905, B_906]: (k4_xboole_0(k3_xboole_0(A_904, C_905), B_906)=k1_xboole_0 | ~r1_tarski(A_904, B_906))), inference(resolution, [status(thm)], [c_86607, c_8])).
% 30.20/18.56  tff(c_86726, plain, (![C_916, A_917, B_918]: (k4_xboole_0(k2_zfmisc_1(C_916, A_917), k2_zfmisc_1(C_916, B_918))=k2_zfmisc_1(C_916, k4_xboole_0(A_917, B_918)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_86755, plain, (![A_15, A_917]: (k4_xboole_0(k2_zfmisc_1(A_15, A_917), k1_xboole_0)=k2_zfmisc_1(A_15, k4_xboole_0(A_917, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_86726])).
% 30.20/18.56  tff(c_86868, plain, (![A_929, C_930, B_931]: (k4_xboole_0(k2_zfmisc_1(A_929, C_930), k2_zfmisc_1(B_931, C_930))=k2_zfmisc_1(k4_xboole_0(A_929, B_931), C_930))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.20/18.56  tff(c_86899, plain, (![A_929, B_16]: (k4_xboole_0(k2_zfmisc_1(A_929, B_16), k1_xboole_0)=k2_zfmisc_1(k4_xboole_0(A_929, k1_xboole_0), B_16))), inference(superposition, [status(thm), theory('equality')], [c_22, c_86868])).
% 30.20/18.56  tff(c_87062, plain, (![A_942, B_943]: (k2_zfmisc_1(k4_xboole_0(A_942, k1_xboole_0), B_943)=k2_zfmisc_1(A_942, k4_xboole_0(B_943, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_86755, c_86899])).
% 30.20/18.56  tff(c_87112, plain, (![A_904, C_905, B_943]: (k2_zfmisc_1(k3_xboole_0(A_904, C_905), k4_xboole_0(B_943, k1_xboole_0))=k2_zfmisc_1(k1_xboole_0, B_943) | ~r1_tarski(A_904, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86627, c_87062])).
% 30.20/18.56  tff(c_90617, plain, (![A_1425, C_1426, B_1427]: (k2_zfmisc_1(k3_xboole_0(A_1425, C_1426), k4_xboole_0(B_1427, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(A_1425, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_87112])).
% 30.20/18.56  tff(c_90702, plain, (![B_1427]: (k2_zfmisc_1('#skF_1', k4_xboole_0(B_1427, k1_xboole_0))=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86601, c_90617])).
% 30.20/18.56  tff(c_91043, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_90702])).
% 30.20/18.56  tff(c_134004, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133862, c_91043])).
% 30.20/18.56  tff(c_134052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134013, c_134004])).
% 30.20/18.56  tff(c_134054, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_90702])).
% 30.20/18.56  tff(c_87443, plain, (![A_953, A_3]: (k3_xboole_0(A_953, A_3)=A_3 | ~r1_tarski(A_3, A_953))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87431])).
% 30.20/18.56  tff(c_134070, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_134054, c_87443])).
% 30.20/18.56  tff(c_89683, plain, (![C_1389]: (k3_xboole_0(k1_xboole_0, C_1389)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_88957])).
% 30.20/18.56  tff(c_134096, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_134070, c_89683])).
% 30.20/18.56  tff(c_134195, plain, (![B_16]: (k2_zfmisc_1('#skF_1', B_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134096, c_134096, c_22])).
% 30.20/18.56  tff(c_134198, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134096, c_32])).
% 30.20/18.56  tff(c_134422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134195, c_134198])).
% 30.20/18.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.20/18.56  
% 30.20/18.56  Inference rules
% 30.20/18.56  ----------------------
% 30.20/18.56  #Ref     : 0
% 30.20/18.56  #Sup     : 34620
% 30.20/18.56  #Fact    : 0
% 30.20/18.56  #Define  : 0
% 30.20/18.56  #Split   : 30
% 30.20/18.56  #Chain   : 0
% 30.20/18.56  #Close   : 0
% 30.20/18.56  
% 30.20/18.56  Ordering : KBO
% 30.20/18.56  
% 30.20/18.56  Simplification rules
% 30.20/18.56  ----------------------
% 30.20/18.56  #Subsume      : 8662
% 30.20/18.56  #Demod        : 19994
% 30.20/18.56  #Tautology    : 11166
% 30.20/18.56  #SimpNegUnit  : 42
% 30.20/18.56  #BackRed      : 486
% 30.20/18.56  
% 30.20/18.56  #Partial instantiations: 192
% 30.20/18.56  #Strategies tried      : 1
% 30.20/18.56  
% 30.20/18.56  Timing (in seconds)
% 30.20/18.56  ----------------------
% 30.20/18.56  Preprocessing        : 0.29
% 30.20/18.56  Parsing              : 0.16
% 30.20/18.56  CNF conversion       : 0.02
% 30.20/18.56  Main loop            : 17.48
% 30.20/18.56  Inferencing          : 2.57
% 30.20/18.56  Reduction            : 6.99
% 30.20/18.56  Demodulation         : 5.86
% 30.20/18.56  BG Simplification    : 0.39
% 30.20/18.56  Subsumption          : 6.38
% 30.20/18.56  Abstraction          : 0.55
% 30.20/18.56  MUC search           : 0.00
% 30.20/18.56  Cooper               : 0.00
% 30.20/18.56  Total                : 17.84
% 30.20/18.56  Index Insertion      : 0.00
% 30.20/18.56  Index Deletion       : 0.00
% 30.20/18.56  Index Matching       : 0.00
% 30.20/18.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
