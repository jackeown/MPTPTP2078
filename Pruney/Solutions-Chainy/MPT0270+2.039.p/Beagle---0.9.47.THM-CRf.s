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
% DateTime   : Thu Dec  3 09:52:58 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 637 expanded)
%              Number of leaves         :   29 ( 224 expanded)
%              Depth                    :   20
%              Number of atoms          :  244 (1168 expanded)
%              Number of equality atoms :   93 ( 485 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_140,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_38,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,A_49)
      | ~ r2_hidden(D_48,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_49,B_50)),A_49)
      | k3_xboole_0(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_36,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_400,plain,(
    ! [A_85,C_86,B_87] :
      ( ~ r2_hidden(A_85,C_86)
      | ~ r2_hidden(A_85,B_87)
      | ~ r2_hidden(A_85,k5_xboole_0(B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_976,plain,(
    ! [A_123,A_124,B_125] :
      ( ~ r2_hidden(A_123,k3_xboole_0(A_124,B_125))
      | ~ r2_hidden(A_123,A_124)
      | ~ r2_hidden(A_123,k4_xboole_0(A_124,B_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_400])).

tff(c_1238,plain,(
    ! [A_135,A_136] :
      ( ~ r2_hidden(A_135,k3_xboole_0(A_136,k1_xboole_0))
      | ~ r2_hidden(A_135,A_136)
      | ~ r2_hidden(A_135,A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_976])).

tff(c_1403,plain,(
    ! [A_142] :
      ( ~ r2_hidden('#skF_3'(k3_xboole_0(A_142,k1_xboole_0)),A_142)
      | k3_xboole_0(A_142,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_1238])).

tff(c_1509,plain,(
    ! [A_143] : k3_xboole_0(A_143,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179,c_1403])).

tff(c_1539,plain,(
    ! [A_143] : k5_xboole_0(A_143,k1_xboole_0) = k4_xboole_0(A_143,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_36])).

tff(c_1562,plain,(
    ! [A_143] : k5_xboole_0(A_143,k1_xboole_0) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1539])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_253,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_63,B_64)),A_63)
      | k3_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_271,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_1,B_2)),B_2)
      | k3_xboole_0(B_2,A_1) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_1456,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_1403])).

tff(c_141,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_1486,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_150])).

tff(c_1503,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1486])).

tff(c_1611,plain,(
    ! [B_147] : k3_xboole_0(k1_xboole_0,B_147) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1509])).

tff(c_1648,plain,(
    ! [B_147] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_36])).

tff(c_1710,plain,(
    ! [B_149] : k4_xboole_0(k1_xboole_0,B_149) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1648])).

tff(c_54,plain,(
    ! [B_31,A_30] :
      ( ~ r2_hidden(B_31,A_30)
      | k4_xboole_0(A_30,k1_tarski(B_31)) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1772,plain,(
    ! [B_31] : ~ r2_hidden(B_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_54])).

tff(c_1558,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1509])).

tff(c_566,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_1'(A_97,B_98,C_99),A_97)
      | r2_hidden('#skF_2'(A_97,B_98,C_99),C_99)
      | k3_xboole_0(A_97,B_98) = C_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3668,plain,(
    ! [A_193,B_194,A_195,B_196] :
      ( r2_hidden('#skF_2'(A_193,B_194,k3_xboole_0(A_195,B_196)),A_195)
      | r2_hidden('#skF_1'(A_193,B_194,k3_xboole_0(A_195,B_196)),A_193)
      | k3_xboole_0(A_195,B_196) = k3_xboole_0(A_193,B_194) ) ),
    inference(resolution,[status(thm)],[c_566,c_8])).

tff(c_3779,plain,(
    ! [A_193,B_194,B_2] :
      ( r2_hidden('#skF_2'(A_193,B_194,k3_xboole_0(k1_xboole_0,B_2)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_193,B_194,k1_xboole_0),A_193)
      | k3_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(A_193,B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1558,c_3668])).

tff(c_3827,plain,(
    ! [A_193,B_194] :
      ( r2_hidden('#skF_2'(A_193,B_194,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_193,B_194,k1_xboole_0),A_193)
      | k3_xboole_0(A_193,B_194) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_3779])).

tff(c_3903,plain,(
    ! [A_199,B_200] :
      ( r2_hidden('#skF_1'(A_199,B_200,k1_xboole_0),A_199)
      | k3_xboole_0(A_199,B_200) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1772,c_3827])).

tff(c_861,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_1'(A_118,B_119,C_120),B_119)
      | r2_hidden('#skF_2'(A_118,B_119,C_120),C_120)
      | k3_xboole_0(A_118,B_119) = C_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_922,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119,B_119),B_119)
      | k3_xboole_0(A_118,B_119) = B_119 ) ),
    inference(resolution,[status(thm)],[c_861,c_16])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1205,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_1'(A_132,B_133,C_134),A_132)
      | ~ r2_hidden('#skF_2'(A_132,B_133,C_134),B_133)
      | ~ r2_hidden('#skF_2'(A_132,B_133,C_134),A_132)
      | k3_xboole_0(A_132,B_133) = C_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2128,plain,(
    ! [A_157,C_158] :
      ( ~ r2_hidden('#skF_2'(A_157,C_158,C_158),A_157)
      | r2_hidden('#skF_1'(A_157,C_158,C_158),A_157)
      | k3_xboole_0(A_157,C_158) = C_158 ) ),
    inference(resolution,[status(thm)],[c_20,c_1205])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2251,plain,(
    ! [A_160] :
      ( ~ r2_hidden('#skF_2'(A_160,A_160,A_160),A_160)
      | k3_xboole_0(A_160,A_160) = A_160 ) ),
    inference(resolution,[status(thm)],[c_2128,c_10])).

tff(c_2306,plain,(
    ! [B_161] : k3_xboole_0(B_161,B_161) = B_161 ),
    inference(resolution,[status(thm)],[c_922,c_2251])).

tff(c_2347,plain,(
    ! [B_161] : k5_xboole_0(B_161,B_161) = k4_xboole_0(B_161,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_150])).

tff(c_364,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(A_82,B_83)
      | r2_hidden(A_82,C_84)
      | ~ r2_hidden(A_82,k5_xboole_0(B_83,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_399,plain,(
    ! [B_83,C_84] :
      ( r2_hidden('#skF_3'(k5_xboole_0(B_83,C_84)),B_83)
      | r2_hidden('#skF_3'(k5_xboole_0(B_83,C_84)),C_84)
      | k5_xboole_0(B_83,C_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_1862,plain,(
    ! [B_83] :
      ( k5_xboole_0(B_83,B_83) = k1_xboole_0
      | r2_hidden('#skF_3'(k5_xboole_0(B_83,B_83)),B_83) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_399])).

tff(c_2379,plain,(
    ! [B_83] :
      ( k4_xboole_0(B_83,B_83) = k1_xboole_0
      | r2_hidden('#skF_3'(k4_xboole_0(B_83,B_83)),B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_2347,c_1862])).

tff(c_2380,plain,(
    ! [B_162] : k5_xboole_0(B_162,B_162) = k4_xboole_0(B_162,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_150])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( ~ r2_hidden(A_9,C_11)
      | ~ r2_hidden(A_9,B_10)
      | ~ r2_hidden(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2955,plain,(
    ! [A_174,B_175] :
      ( ~ r2_hidden(A_174,B_175)
      | ~ r2_hidden(A_174,B_175)
      | ~ r2_hidden(A_174,k4_xboole_0(B_175,B_175)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2380,c_22])).

tff(c_3086,plain,(
    ! [B_176] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(B_176,B_176)),B_176)
      | k4_xboole_0(B_176,B_176) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_2955])).

tff(c_3142,plain,(
    ! [B_177] : k4_xboole_0(B_177,B_177) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2379,c_3086])).

tff(c_48,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(A_27,k4_xboole_0(B_28,k1_tarski(C_29)))
      | C_29 = A_27
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3165,plain,(
    ! [A_27,C_29] :
      ( r2_hidden(A_27,k1_xboole_0)
      | C_29 = A_27
      | ~ r2_hidden(A_27,k1_tarski(C_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3142,c_48])).

tff(c_3207,plain,(
    ! [C_29,A_27] :
      ( C_29 = A_27
      | ~ r2_hidden(A_27,k1_tarski(C_29)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1772,c_3165])).

tff(c_4094,plain,(
    ! [C_205,B_206] :
      ( '#skF_1'(k1_tarski(C_205),B_206,k1_xboole_0) = C_205
      | k3_xboole_0(k1_tarski(C_205),B_206) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3903,c_3207])).

tff(c_4162,plain,(
    ! [C_205,B_206] :
      ( k5_xboole_0(k1_tarski(C_205),k1_xboole_0) = k4_xboole_0(k1_tarski(C_205),B_206)
      | '#skF_1'(k1_tarski(C_205),B_206,k1_xboole_0) = C_205 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4094,c_36])).

tff(c_7320,plain,(
    ! [C_290,B_291] :
      ( k4_xboole_0(k1_tarski(C_290),B_291) = k1_tarski(C_290)
      | '#skF_1'(k1_tarski(C_290),B_291,k1_xboole_0) = C_290 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_4162])).

tff(c_7415,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5',k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7320,c_140])).

tff(c_3260,plain,(
    ! [A_179,B_180,A_181,B_182] :
      ( r2_hidden('#skF_2'(A_179,B_180,k3_xboole_0(A_181,B_182)),A_181)
      | r2_hidden('#skF_1'(A_179,B_180,k3_xboole_0(A_181,B_182)),B_180)
      | k3_xboole_0(A_181,B_182) = k3_xboole_0(A_179,B_180) ) ),
    inference(resolution,[status(thm)],[c_861,c_8])).

tff(c_3369,plain,(
    ! [A_179,B_180,B_2] :
      ( r2_hidden('#skF_2'(A_179,B_180,k3_xboole_0(k1_xboole_0,B_2)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_179,B_180,k1_xboole_0),B_180)
      | k3_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(A_179,B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1558,c_3260])).

tff(c_3417,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_2'(A_179,B_180,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_179,B_180,k1_xboole_0),B_180)
      | k3_xboole_0(A_179,B_180) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_3369])).

tff(c_3418,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_1'(A_179,B_180,k1_xboole_0),B_180)
      | k3_xboole_0(A_179,B_180) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1772,c_3417])).

tff(c_7431,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7415,c_3418])).

tff(c_7449,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7431])).

tff(c_7450,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_7449])).

tff(c_7563,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7450,c_150])).

tff(c_7614,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_7563])).

tff(c_7616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_7614])).

tff(c_7617,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7639,plain,(
    ! [D_296,A_297,B_298] :
      ( r2_hidden(D_296,A_297)
      | ~ r2_hidden(D_296,k3_xboole_0(A_297,B_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7650,plain,(
    ! [A_297,B_298] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_297,B_298)),A_297)
      | k3_xboole_0(A_297,B_298) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_7639])).

tff(c_7854,plain,(
    ! [A_323,C_324,B_325] :
      ( ~ r2_hidden(A_323,C_324)
      | ~ r2_hidden(A_323,B_325)
      | ~ r2_hidden(A_323,k5_xboole_0(B_325,C_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8111,plain,(
    ! [A_348,A_349,B_350] :
      ( ~ r2_hidden(A_348,k3_xboole_0(A_349,B_350))
      | ~ r2_hidden(A_348,A_349)
      | ~ r2_hidden(A_348,k4_xboole_0(A_349,B_350)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7854])).

tff(c_8340,plain,(
    ! [A_360,A_361] :
      ( ~ r2_hidden(A_360,k3_xboole_0(A_361,k1_xboole_0))
      | ~ r2_hidden(A_360,A_361)
      | ~ r2_hidden(A_360,A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8111])).

tff(c_8532,plain,(
    ! [A_366] :
      ( ~ r2_hidden('#skF_3'(k3_xboole_0(A_366,k1_xboole_0)),A_366)
      | k3_xboole_0(A_366,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_8340])).

tff(c_8659,plain,(
    ! [A_370] : k3_xboole_0(A_370,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7650,c_8532])).

tff(c_8685,plain,(
    ! [A_370] : k5_xboole_0(A_370,k1_xboole_0) = k4_xboole_0(A_370,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8659,c_36])).

tff(c_8708,plain,(
    ! [A_370] : k5_xboole_0(A_370,k1_xboole_0) = A_370 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8685])).

tff(c_7735,plain,(
    ! [A_311,B_312] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_311,B_312)),A_311)
      | k3_xboole_0(A_311,B_312) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_7639])).

tff(c_7753,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_1,B_2)),B_2)
      | k3_xboole_0(B_2,A_1) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7735])).

tff(c_7618,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7780,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7618,c_62])).

tff(c_8132,plain,(
    ! [A_348] :
      ( ~ r2_hidden(A_348,k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
      | ~ r2_hidden(A_348,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_348,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7780,c_8111])).

tff(c_8710,plain,(
    ! [A_371] :
      ( ~ r2_hidden(A_371,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden(A_371,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_371,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8132])).

tff(c_8760,plain,
    ( ~ r2_hidden('#skF_3'(k3_xboole_0('#skF_7',k1_tarski('#skF_6'))),k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_8710])).

tff(c_9264,plain,(
    ~ r2_hidden('#skF_3'(k3_xboole_0('#skF_7',k1_tarski('#skF_6'))),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_8760])).

tff(c_9271,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7753,c_9264])).

tff(c_7623,plain,(
    ! [A_292,B_293] : k5_xboole_0(A_292,k3_xboole_0(A_292,B_293)) = k4_xboole_0(A_292,B_293) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7635,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7623])).

tff(c_9291,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k5_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9271,c_7635])).

tff(c_9318,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8708,c_9291])).

tff(c_9408,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9318,c_54])).

tff(c_9427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_9408])).

tff(c_9428,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8760])).

tff(c_9458,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k5_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9428,c_36])).

tff(c_9470,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8708,c_9458])).

tff(c_9495,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9470,c_54])).

tff(c_9514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_9495])).

tff(c_9515,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9771,plain,(
    ! [A_423,C_424,B_425] :
      ( r2_hidden(A_423,C_424)
      | ~ r2_hidden(A_423,B_425)
      | r2_hidden(A_423,k5_xboole_0(B_425,C_424)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10060,plain,(
    ! [A_451,A_452,B_453] :
      ( r2_hidden(A_451,k3_xboole_0(A_452,B_453))
      | ~ r2_hidden(A_451,A_452)
      | r2_hidden(A_451,k4_xboole_0(A_452,B_453)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9771])).

tff(c_50,plain,(
    ! [C_29,B_28] : ~ r2_hidden(C_29,k4_xboole_0(B_28,k1_tarski(C_29))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10084,plain,(
    ! [A_454,A_455] :
      ( r2_hidden(A_454,k3_xboole_0(A_455,k1_tarski(A_454)))
      | ~ r2_hidden(A_454,A_455) ) ),
    inference(resolution,[status(thm)],[c_10060,c_50])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10101,plain,(
    ! [A_456,A_457] :
      ( r2_hidden(A_456,k1_tarski(A_456))
      | ~ r2_hidden(A_456,A_457) ) ),
    inference(resolution,[status(thm)],[c_10084,c_6])).

tff(c_10151,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9515,c_10101])).

tff(c_10082,plain,(
    ! [A_451,A_452] :
      ( r2_hidden(A_451,k3_xboole_0(A_452,k1_tarski(A_451)))
      | ~ r2_hidden(A_451,A_452) ) ),
    inference(resolution,[status(thm)],[c_10060,c_50])).

tff(c_9516,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9654,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9516,c_64])).

tff(c_9809,plain,(
    ! [A_436,C_437,B_438] :
      ( ~ r2_hidden(A_436,C_437)
      | ~ r2_hidden(A_436,B_438)
      | ~ r2_hidden(A_436,k5_xboole_0(B_438,C_437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10185,plain,(
    ! [A_461,A_462,B_463] :
      ( ~ r2_hidden(A_461,k3_xboole_0(A_462,B_463))
      | ~ r2_hidden(A_461,A_462)
      | ~ r2_hidden(A_461,k4_xboole_0(A_462,B_463)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9809])).

tff(c_10229,plain,(
    ! [A_461] :
      ( ~ r2_hidden(A_461,k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
      | ~ r2_hidden(A_461,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_461,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9654,c_10185])).

tff(c_10460,plain,(
    ! [A_473] :
      ( ~ r2_hidden(A_473,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden(A_473,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_473,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10229])).

tff(c_10472,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10082,c_10460])).

tff(c_10518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9515,c_10151,c_10472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.72  
% 7.94/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.72  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 7.94/2.72  
% 7.94/2.72  %Foreground sorts:
% 7.94/2.72  
% 7.94/2.72  
% 7.94/2.72  %Background operators:
% 7.94/2.72  
% 7.94/2.72  
% 7.94/2.72  %Foreground operators:
% 7.94/2.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.94/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.94/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.94/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.94/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.94/2.72  tff('#skF_7', type, '#skF_7': $i).
% 7.94/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.94/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.94/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.94/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.94/2.72  tff('#skF_6', type, '#skF_6': $i).
% 7.94/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.94/2.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.94/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.94/2.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.94/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/2.72  
% 7.94/2.74  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 7.94/2.74  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.94/2.74  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.94/2.74  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.94/2.74  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.94/2.74  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.94/2.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.94/2.74  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.94/2.74  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.94/2.74  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.94/2.74  tff(c_140, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 7.94/2.74  tff(c_38, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.94/2.74  tff(c_34, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.94/2.74  tff(c_168, plain, (![D_48, A_49, B_50]: (r2_hidden(D_48, A_49) | ~r2_hidden(D_48, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_179, plain, (![A_49, B_50]: (r2_hidden('#skF_3'(k3_xboole_0(A_49, B_50)), A_49) | k3_xboole_0(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_168])).
% 7.94/2.74  tff(c_36, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_400, plain, (![A_85, C_86, B_87]: (~r2_hidden(A_85, C_86) | ~r2_hidden(A_85, B_87) | ~r2_hidden(A_85, k5_xboole_0(B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_976, plain, (![A_123, A_124, B_125]: (~r2_hidden(A_123, k3_xboole_0(A_124, B_125)) | ~r2_hidden(A_123, A_124) | ~r2_hidden(A_123, k4_xboole_0(A_124, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_400])).
% 7.94/2.74  tff(c_1238, plain, (![A_135, A_136]: (~r2_hidden(A_135, k3_xboole_0(A_136, k1_xboole_0)) | ~r2_hidden(A_135, A_136) | ~r2_hidden(A_135, A_136))), inference(superposition, [status(thm), theory('equality')], [c_38, c_976])).
% 7.94/2.74  tff(c_1403, plain, (![A_142]: (~r2_hidden('#skF_3'(k3_xboole_0(A_142, k1_xboole_0)), A_142) | k3_xboole_0(A_142, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_1238])).
% 7.94/2.74  tff(c_1509, plain, (![A_143]: (k3_xboole_0(A_143, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_179, c_1403])).
% 7.94/2.74  tff(c_1539, plain, (![A_143]: (k5_xboole_0(A_143, k1_xboole_0)=k4_xboole_0(A_143, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1509, c_36])).
% 7.94/2.74  tff(c_1562, plain, (![A_143]: (k5_xboole_0(A_143, k1_xboole_0)=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1539])).
% 7.94/2.74  tff(c_60, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.94/2.74  tff(c_85, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 7.94/2.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.94/2.74  tff(c_253, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(k3_xboole_0(A_63, B_64)), A_63) | k3_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_168])).
% 7.94/2.74  tff(c_271, plain, (![A_1, B_2]: (r2_hidden('#skF_3'(k3_xboole_0(A_1, B_2)), B_2) | k3_xboole_0(B_2, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_253])).
% 7.94/2.74  tff(c_1456, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_1403])).
% 7.94/2.74  tff(c_141, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_150, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 7.94/2.74  tff(c_1486, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1456, c_150])).
% 7.94/2.74  tff(c_1503, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1486])).
% 7.94/2.74  tff(c_1611, plain, (![B_147]: (k3_xboole_0(k1_xboole_0, B_147)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1509])).
% 7.94/2.74  tff(c_1648, plain, (![B_147]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_147))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_36])).
% 7.94/2.74  tff(c_1710, plain, (![B_149]: (k4_xboole_0(k1_xboole_0, B_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1648])).
% 7.94/2.74  tff(c_54, plain, (![B_31, A_30]: (~r2_hidden(B_31, A_30) | k4_xboole_0(A_30, k1_tarski(B_31))!=A_30)), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.94/2.74  tff(c_1772, plain, (![B_31]: (~r2_hidden(B_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1710, c_54])).
% 7.94/2.74  tff(c_1558, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1509])).
% 7.94/2.74  tff(c_566, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_1'(A_97, B_98, C_99), A_97) | r2_hidden('#skF_2'(A_97, B_98, C_99), C_99) | k3_xboole_0(A_97, B_98)=C_99)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_3668, plain, (![A_193, B_194, A_195, B_196]: (r2_hidden('#skF_2'(A_193, B_194, k3_xboole_0(A_195, B_196)), A_195) | r2_hidden('#skF_1'(A_193, B_194, k3_xboole_0(A_195, B_196)), A_193) | k3_xboole_0(A_195, B_196)=k3_xboole_0(A_193, B_194))), inference(resolution, [status(thm)], [c_566, c_8])).
% 7.94/2.74  tff(c_3779, plain, (![A_193, B_194, B_2]: (r2_hidden('#skF_2'(A_193, B_194, k3_xboole_0(k1_xboole_0, B_2)), k1_xboole_0) | r2_hidden('#skF_1'(A_193, B_194, k1_xboole_0), A_193) | k3_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(A_193, B_194))), inference(superposition, [status(thm), theory('equality')], [c_1558, c_3668])).
% 7.94/2.74  tff(c_3827, plain, (![A_193, B_194]: (r2_hidden('#skF_2'(A_193, B_194, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_193, B_194, k1_xboole_0), A_193) | k3_xboole_0(A_193, B_194)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_3779])).
% 7.94/2.74  tff(c_3903, plain, (![A_199, B_200]: (r2_hidden('#skF_1'(A_199, B_200, k1_xboole_0), A_199) | k3_xboole_0(A_199, B_200)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1772, c_3827])).
% 7.94/2.74  tff(c_861, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_1'(A_118, B_119, C_120), B_119) | r2_hidden('#skF_2'(A_118, B_119, C_120), C_120) | k3_xboole_0(A_118, B_119)=C_120)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_922, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119, B_119), B_119) | k3_xboole_0(A_118, B_119)=B_119)), inference(resolution, [status(thm)], [c_861, c_16])).
% 7.94/2.74  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_1205, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_1'(A_132, B_133, C_134), A_132) | ~r2_hidden('#skF_2'(A_132, B_133, C_134), B_133) | ~r2_hidden('#skF_2'(A_132, B_133, C_134), A_132) | k3_xboole_0(A_132, B_133)=C_134)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_2128, plain, (![A_157, C_158]: (~r2_hidden('#skF_2'(A_157, C_158, C_158), A_157) | r2_hidden('#skF_1'(A_157, C_158, C_158), A_157) | k3_xboole_0(A_157, C_158)=C_158)), inference(resolution, [status(thm)], [c_20, c_1205])).
% 7.94/2.74  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_2251, plain, (![A_160]: (~r2_hidden('#skF_2'(A_160, A_160, A_160), A_160) | k3_xboole_0(A_160, A_160)=A_160)), inference(resolution, [status(thm)], [c_2128, c_10])).
% 7.94/2.74  tff(c_2306, plain, (![B_161]: (k3_xboole_0(B_161, B_161)=B_161)), inference(resolution, [status(thm)], [c_922, c_2251])).
% 7.94/2.74  tff(c_2347, plain, (![B_161]: (k5_xboole_0(B_161, B_161)=k4_xboole_0(B_161, B_161))), inference(superposition, [status(thm), theory('equality')], [c_2306, c_150])).
% 7.94/2.74  tff(c_364, plain, (![A_82, B_83, C_84]: (r2_hidden(A_82, B_83) | r2_hidden(A_82, C_84) | ~r2_hidden(A_82, k5_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_399, plain, (![B_83, C_84]: (r2_hidden('#skF_3'(k5_xboole_0(B_83, C_84)), B_83) | r2_hidden('#skF_3'(k5_xboole_0(B_83, C_84)), C_84) | k5_xboole_0(B_83, C_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_364])).
% 7.94/2.74  tff(c_1862, plain, (![B_83]: (k5_xboole_0(B_83, B_83)=k1_xboole_0 | r2_hidden('#skF_3'(k5_xboole_0(B_83, B_83)), B_83))), inference(factorization, [status(thm), theory('equality')], [c_399])).
% 7.94/2.74  tff(c_2379, plain, (![B_83]: (k4_xboole_0(B_83, B_83)=k1_xboole_0 | r2_hidden('#skF_3'(k4_xboole_0(B_83, B_83)), B_83))), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_2347, c_1862])).
% 7.94/2.74  tff(c_2380, plain, (![B_162]: (k5_xboole_0(B_162, B_162)=k4_xboole_0(B_162, B_162))), inference(superposition, [status(thm), theory('equality')], [c_2306, c_150])).
% 7.94/2.74  tff(c_22, plain, (![A_9, C_11, B_10]: (~r2_hidden(A_9, C_11) | ~r2_hidden(A_9, B_10) | ~r2_hidden(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_2955, plain, (![A_174, B_175]: (~r2_hidden(A_174, B_175) | ~r2_hidden(A_174, B_175) | ~r2_hidden(A_174, k4_xboole_0(B_175, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_2380, c_22])).
% 7.94/2.74  tff(c_3086, plain, (![B_176]: (~r2_hidden('#skF_3'(k4_xboole_0(B_176, B_176)), B_176) | k4_xboole_0(B_176, B_176)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2955])).
% 7.94/2.74  tff(c_3142, plain, (![B_177]: (k4_xboole_0(B_177, B_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2379, c_3086])).
% 7.94/2.74  tff(c_48, plain, (![A_27, B_28, C_29]: (r2_hidden(A_27, k4_xboole_0(B_28, k1_tarski(C_29))) | C_29=A_27 | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.94/2.74  tff(c_3165, plain, (![A_27, C_29]: (r2_hidden(A_27, k1_xboole_0) | C_29=A_27 | ~r2_hidden(A_27, k1_tarski(C_29)))), inference(superposition, [status(thm), theory('equality')], [c_3142, c_48])).
% 7.94/2.74  tff(c_3207, plain, (![C_29, A_27]: (C_29=A_27 | ~r2_hidden(A_27, k1_tarski(C_29)))), inference(negUnitSimplification, [status(thm)], [c_1772, c_3165])).
% 7.94/2.74  tff(c_4094, plain, (![C_205, B_206]: ('#skF_1'(k1_tarski(C_205), B_206, k1_xboole_0)=C_205 | k3_xboole_0(k1_tarski(C_205), B_206)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3903, c_3207])).
% 7.94/2.74  tff(c_4162, plain, (![C_205, B_206]: (k5_xboole_0(k1_tarski(C_205), k1_xboole_0)=k4_xboole_0(k1_tarski(C_205), B_206) | '#skF_1'(k1_tarski(C_205), B_206, k1_xboole_0)=C_205)), inference(superposition, [status(thm), theory('equality')], [c_4094, c_36])).
% 7.94/2.74  tff(c_7320, plain, (![C_290, B_291]: (k4_xboole_0(k1_tarski(C_290), B_291)=k1_tarski(C_290) | '#skF_1'(k1_tarski(C_290), B_291, k1_xboole_0)=C_290)), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_4162])).
% 7.94/2.74  tff(c_7415, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5', k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7320, c_140])).
% 7.94/2.74  tff(c_3260, plain, (![A_179, B_180, A_181, B_182]: (r2_hidden('#skF_2'(A_179, B_180, k3_xboole_0(A_181, B_182)), A_181) | r2_hidden('#skF_1'(A_179, B_180, k3_xboole_0(A_181, B_182)), B_180) | k3_xboole_0(A_181, B_182)=k3_xboole_0(A_179, B_180))), inference(resolution, [status(thm)], [c_861, c_8])).
% 7.94/2.74  tff(c_3369, plain, (![A_179, B_180, B_2]: (r2_hidden('#skF_2'(A_179, B_180, k3_xboole_0(k1_xboole_0, B_2)), k1_xboole_0) | r2_hidden('#skF_1'(A_179, B_180, k1_xboole_0), B_180) | k3_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(A_179, B_180))), inference(superposition, [status(thm), theory('equality')], [c_1558, c_3260])).
% 7.94/2.74  tff(c_3417, plain, (![A_179, B_180]: (r2_hidden('#skF_2'(A_179, B_180, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_179, B_180, k1_xboole_0), B_180) | k3_xboole_0(A_179, B_180)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_3369])).
% 7.94/2.74  tff(c_3418, plain, (![A_179, B_180]: (r2_hidden('#skF_1'(A_179, B_180, k1_xboole_0), B_180) | k3_xboole_0(A_179, B_180)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1772, c_3417])).
% 7.94/2.74  tff(c_7431, plain, (r2_hidden('#skF_4', '#skF_5') | k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7415, c_3418])).
% 7.94/2.74  tff(c_7449, plain, (r2_hidden('#skF_4', '#skF_5') | k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7431])).
% 7.94/2.74  tff(c_7450, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_85, c_7449])).
% 7.94/2.74  tff(c_7563, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7450, c_150])).
% 7.94/2.74  tff(c_7614, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_7563])).
% 7.94/2.74  tff(c_7616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_7614])).
% 7.94/2.74  tff(c_7617, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 7.94/2.74  tff(c_7639, plain, (![D_296, A_297, B_298]: (r2_hidden(D_296, A_297) | ~r2_hidden(D_296, k3_xboole_0(A_297, B_298)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_7650, plain, (![A_297, B_298]: (r2_hidden('#skF_3'(k3_xboole_0(A_297, B_298)), A_297) | k3_xboole_0(A_297, B_298)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_7639])).
% 7.94/2.74  tff(c_7854, plain, (![A_323, C_324, B_325]: (~r2_hidden(A_323, C_324) | ~r2_hidden(A_323, B_325) | ~r2_hidden(A_323, k5_xboole_0(B_325, C_324)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_8111, plain, (![A_348, A_349, B_350]: (~r2_hidden(A_348, k3_xboole_0(A_349, B_350)) | ~r2_hidden(A_348, A_349) | ~r2_hidden(A_348, k4_xboole_0(A_349, B_350)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_7854])).
% 7.94/2.74  tff(c_8340, plain, (![A_360, A_361]: (~r2_hidden(A_360, k3_xboole_0(A_361, k1_xboole_0)) | ~r2_hidden(A_360, A_361) | ~r2_hidden(A_360, A_361))), inference(superposition, [status(thm), theory('equality')], [c_38, c_8111])).
% 7.94/2.74  tff(c_8532, plain, (![A_366]: (~r2_hidden('#skF_3'(k3_xboole_0(A_366, k1_xboole_0)), A_366) | k3_xboole_0(A_366, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_8340])).
% 7.94/2.74  tff(c_8659, plain, (![A_370]: (k3_xboole_0(A_370, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7650, c_8532])).
% 7.94/2.74  tff(c_8685, plain, (![A_370]: (k5_xboole_0(A_370, k1_xboole_0)=k4_xboole_0(A_370, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8659, c_36])).
% 7.94/2.74  tff(c_8708, plain, (![A_370]: (k5_xboole_0(A_370, k1_xboole_0)=A_370)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8685])).
% 7.94/2.74  tff(c_7735, plain, (![A_311, B_312]: (r2_hidden('#skF_3'(k3_xboole_0(A_311, B_312)), A_311) | k3_xboole_0(A_311, B_312)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_7639])).
% 7.94/2.74  tff(c_7753, plain, (![A_1, B_2]: (r2_hidden('#skF_3'(k3_xboole_0(A_1, B_2)), B_2) | k3_xboole_0(B_2, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_7735])).
% 7.94/2.74  tff(c_7618, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 7.94/2.74  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.94/2.74  tff(c_7780, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7618, c_62])).
% 7.94/2.74  tff(c_8132, plain, (![A_348]: (~r2_hidden(A_348, k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | ~r2_hidden(A_348, k1_tarski('#skF_6')) | ~r2_hidden(A_348, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7780, c_8111])).
% 7.94/2.74  tff(c_8710, plain, (![A_371]: (~r2_hidden(A_371, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden(A_371, k1_tarski('#skF_6')) | ~r2_hidden(A_371, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8132])).
% 7.94/2.74  tff(c_8760, plain, (~r2_hidden('#skF_3'(k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_8710])).
% 7.94/2.74  tff(c_9264, plain, (~r2_hidden('#skF_3'(k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_8760])).
% 7.94/2.74  tff(c_9271, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_7753, c_9264])).
% 7.94/2.74  tff(c_7623, plain, (![A_292, B_293]: (k5_xboole_0(A_292, k3_xboole_0(A_292, B_293))=k4_xboole_0(A_292, B_293))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.74  tff(c_7635, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7623])).
% 7.94/2.74  tff(c_9291, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k5_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9271, c_7635])).
% 7.94/2.74  tff(c_9318, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8708, c_9291])).
% 7.94/2.74  tff(c_9408, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9318, c_54])).
% 7.94/2.74  tff(c_9427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7617, c_9408])).
% 7.94/2.74  tff(c_9428, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_8760])).
% 7.94/2.74  tff(c_9458, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k5_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9428, c_36])).
% 7.94/2.74  tff(c_9470, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8708, c_9458])).
% 7.94/2.74  tff(c_9495, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9470, c_54])).
% 7.94/2.74  tff(c_9514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7617, c_9495])).
% 7.94/2.74  tff(c_9515, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 7.94/2.74  tff(c_9771, plain, (![A_423, C_424, B_425]: (r2_hidden(A_423, C_424) | ~r2_hidden(A_423, B_425) | r2_hidden(A_423, k5_xboole_0(B_425, C_424)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_10060, plain, (![A_451, A_452, B_453]: (r2_hidden(A_451, k3_xboole_0(A_452, B_453)) | ~r2_hidden(A_451, A_452) | r2_hidden(A_451, k4_xboole_0(A_452, B_453)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_9771])).
% 7.94/2.74  tff(c_50, plain, (![C_29, B_28]: (~r2_hidden(C_29, k4_xboole_0(B_28, k1_tarski(C_29))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.94/2.74  tff(c_10084, plain, (![A_454, A_455]: (r2_hidden(A_454, k3_xboole_0(A_455, k1_tarski(A_454))) | ~r2_hidden(A_454, A_455))), inference(resolution, [status(thm)], [c_10060, c_50])).
% 7.94/2.74  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.94/2.74  tff(c_10101, plain, (![A_456, A_457]: (r2_hidden(A_456, k1_tarski(A_456)) | ~r2_hidden(A_456, A_457))), inference(resolution, [status(thm)], [c_10084, c_6])).
% 7.94/2.74  tff(c_10151, plain, (r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_9515, c_10101])).
% 7.94/2.74  tff(c_10082, plain, (![A_451, A_452]: (r2_hidden(A_451, k3_xboole_0(A_452, k1_tarski(A_451))) | ~r2_hidden(A_451, A_452))), inference(resolution, [status(thm)], [c_10060, c_50])).
% 7.94/2.74  tff(c_9516, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 7.94/2.74  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.94/2.74  tff(c_9654, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9516, c_64])).
% 7.94/2.74  tff(c_9809, plain, (![A_436, C_437, B_438]: (~r2_hidden(A_436, C_437) | ~r2_hidden(A_436, B_438) | ~r2_hidden(A_436, k5_xboole_0(B_438, C_437)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.74  tff(c_10185, plain, (![A_461, A_462, B_463]: (~r2_hidden(A_461, k3_xboole_0(A_462, B_463)) | ~r2_hidden(A_461, A_462) | ~r2_hidden(A_461, k4_xboole_0(A_462, B_463)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_9809])).
% 7.94/2.74  tff(c_10229, plain, (![A_461]: (~r2_hidden(A_461, k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | ~r2_hidden(A_461, k1_tarski('#skF_6')) | ~r2_hidden(A_461, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9654, c_10185])).
% 7.94/2.74  tff(c_10460, plain, (![A_473]: (~r2_hidden(A_473, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden(A_473, k1_tarski('#skF_6')) | ~r2_hidden(A_473, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10229])).
% 7.94/2.74  tff(c_10472, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10082, c_10460])).
% 7.94/2.74  tff(c_10518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9515, c_10151, c_10472])).
% 7.94/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.74  
% 7.94/2.74  Inference rules
% 7.94/2.74  ----------------------
% 7.94/2.74  #Ref     : 0
% 7.94/2.74  #Sup     : 2396
% 7.94/2.74  #Fact    : 2
% 7.94/2.74  #Define  : 0
% 7.94/2.74  #Split   : 6
% 7.94/2.74  #Chain   : 0
% 7.94/2.74  #Close   : 0
% 7.94/2.74  
% 7.94/2.74  Ordering : KBO
% 7.94/2.74  
% 7.94/2.74  Simplification rules
% 7.94/2.74  ----------------------
% 7.94/2.74  #Subsume      : 519
% 7.94/2.74  #Demod        : 622
% 7.94/2.74  #Tautology    : 582
% 7.94/2.74  #SimpNegUnit  : 103
% 7.94/2.74  #BackRed      : 9
% 7.94/2.74  
% 7.94/2.74  #Partial instantiations: 0
% 7.94/2.74  #Strategies tried      : 1
% 7.94/2.74  
% 7.94/2.74  Timing (in seconds)
% 7.94/2.74  ----------------------
% 7.94/2.75  Preprocessing        : 0.36
% 7.94/2.75  Parsing              : 0.17
% 7.94/2.75  CNF conversion       : 0.03
% 7.94/2.75  Main loop            : 1.53
% 7.94/2.75  Inferencing          : 0.50
% 7.94/2.75  Reduction            : 0.49
% 7.94/2.75  Demodulation         : 0.35
% 7.94/2.75  BG Simplification    : 0.07
% 7.94/2.75  Subsumption          : 0.34
% 7.94/2.75  Abstraction          : 0.09
% 7.94/2.75  MUC search           : 0.00
% 7.94/2.75  Cooper               : 0.00
% 7.94/2.75  Total                : 1.95
% 7.94/2.75  Index Insertion      : 0.00
% 7.94/2.75  Index Deletion       : 0.00
% 7.94/2.75  Index Matching       : 0.00
% 7.94/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
