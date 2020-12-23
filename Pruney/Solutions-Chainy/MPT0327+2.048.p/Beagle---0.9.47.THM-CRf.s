%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 8.12s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  101 (2262 expanded)
%              Number of leaves         :   31 ( 778 expanded)
%              Depth                    :   22
%              Number of atoms          :  100 (2604 expanded)
%              Number of equality atoms :   81 (2142 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_508,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),B_79) = k1_xboole_0
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_32,c_126])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_517,plain,(
    ! [B_79,A_78] :
      ( k2_xboole_0(B_79,k1_tarski(A_78)) = k2_xboole_0(B_79,k1_xboole_0)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_14])).

tff(c_537,plain,(
    ! [B_79,A_78] :
      ( k2_xboole_0(B_79,k1_tarski(A_78)) = B_79
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_517])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_242,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_230])).

tff(c_629,plain,(
    ! [A_84,B_85] : k5_xboole_0(k5_xboole_0(A_84,B_85),k3_xboole_0(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_641,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k5_xboole_0(B_85,k3_xboole_0(A_84,B_85))) = k2_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_18])).

tff(c_684,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_641])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_32] : r1_tarski(A_32,k1_zfmisc_1(k3_tarski(A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_102,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_32] : k3_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = A_32 ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_239,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = k5_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_230])).

tff(c_248,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_239])).

tff(c_681,plain,(
    ! [A_12] : k5_xboole_0(A_12,k3_xboole_0(A_12,k1_xboole_0)) = k2_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_629])).

tff(c_689,plain,(
    ! [A_86] : k5_xboole_0(A_86,k3_xboole_0(A_86,k1_xboole_0)) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_681])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_755,plain,(
    ! [A_87] : k4_xboole_0(A_87,k1_xboole_0) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_8])).

tff(c_121,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_972,plain,(
    ! [A_95] :
      ( k3_xboole_0(A_95,k1_xboole_0) = A_95
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_125])).

tff(c_1194,plain,(
    ! [B_101] :
      ( k3_xboole_0(k1_xboole_0,B_101) = B_101
      | k1_xboole_0 != B_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_972])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1211,plain,(
    ! [B_101] :
      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,B_101),B_101) = k2_xboole_0(k1_xboole_0,B_101)
      | k1_xboole_0 != B_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_20])).

tff(c_1253,plain,(
    ! [B_101] :
      ( k2_xboole_0(k1_xboole_0,B_101) = k1_xboole_0
      | k1_xboole_0 != B_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_248,c_18,c_1211])).

tff(c_713,plain,(
    ! [A_86] : k4_xboole_0(A_86,k1_xboole_0) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_8])).

tff(c_1016,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_641])).

tff(c_445,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_497,plain,(
    ! [A_12,C_77] : k5_xboole_0(A_12,k5_xboole_0(k1_xboole_0,C_77)) = k5_xboole_0(A_12,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_445])).

tff(c_1030,plain,(
    ! [A_12,B_97] : k5_xboole_0(A_12,k4_xboole_0(B_97,k1_xboole_0)) = k5_xboole_0(A_12,k2_xboole_0(k1_xboole_0,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_497])).

tff(c_1370,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k2_xboole_0(k1_xboole_0,B_106)) = k5_xboole_0(A_105,B_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_1030])).

tff(c_1405,plain,(
    ! [A_105,B_101] :
      ( k5_xboole_0(A_105,k1_xboole_0) = k5_xboole_0(A_105,B_101)
      | k1_xboole_0 != B_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_1370])).

tff(c_1443,plain,(
    ! [A_105] : k5_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1405])).

tff(c_2606,plain,(
    ! [A_134,B_135,C_136] : k5_xboole_0(A_134,k5_xboole_0(k3_xboole_0(A_134,B_135),C_136)) = k5_xboole_0(k4_xboole_0(A_134,B_135),C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_445])).

tff(c_2709,plain,(
    ! [A_134,B_135] : k5_xboole_0(k4_xboole_0(A_134,B_135),k3_xboole_0(A_134,B_135)) = k5_xboole_0(A_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2606])).

tff(c_4670,plain,(
    ! [A_165,B_166] : k5_xboole_0(k4_xboole_0(A_165,B_166),k3_xboole_0(A_165,B_166)) = A_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_2709])).

tff(c_5596,plain,(
    ! [A_179,B_180] : k5_xboole_0(k4_xboole_0(A_179,B_180),k3_xboole_0(B_180,A_179)) = A_179 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4670])).

tff(c_2484,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k5_xboole_0(B_133,k5_xboole_0(A_132,B_133))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_248])).

tff(c_1043,plain,(
    ! [A_86] : k5_xboole_0(k1_xboole_0,A_86) = k2_xboole_0(k1_xboole_0,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_1016])).

tff(c_483,plain,(
    ! [A_32,C_77] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_445])).

tff(c_1718,plain,(
    ! [A_113,C_114] : k5_xboole_0(A_113,k5_xboole_0(A_113,C_114)) = k2_xboole_0(k1_xboole_0,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_483])).

tff(c_1792,plain,(
    ! [A_32] : k5_xboole_0(A_32,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_1718])).

tff(c_1810,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_1792])).

tff(c_1717,plain,(
    ! [A_32,C_77] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_77)) = k2_xboole_0(k1_xboole_0,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_483])).

tff(c_1811,plain,(
    ! [A_32,C_77] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1717])).

tff(c_2495,plain,(
    ! [B_133,A_132] : k5_xboole_0(B_133,k5_xboole_0(A_132,B_133)) = k5_xboole_0(A_132,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2484,c_1811])).

tff(c_2590,plain,(
    ! [B_133,A_132] : k5_xboole_0(B_133,k5_xboole_0(A_132,B_133)) = A_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_2495])).

tff(c_7396,plain,(
    ! [B_205,A_206] : k5_xboole_0(k3_xboole_0(B_205,A_206),A_206) = k4_xboole_0(A_206,B_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_5596,c_2590])).

tff(c_490,plain,(
    ! [A_5,B_6,C_77] : k5_xboole_0(A_5,k5_xboole_0(k3_xboole_0(A_5,B_6),C_77)) = k5_xboole_0(k4_xboole_0(A_5,B_6),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_445])).

tff(c_7450,plain,(
    ! [B_205,A_206] : k5_xboole_0(k4_xboole_0(B_205,A_206),A_206) = k5_xboole_0(B_205,k4_xboole_0(A_206,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7396,c_490])).

tff(c_12445,plain,(
    ! [B_261,A_262] : k5_xboole_0(k4_xboole_0(B_261,A_262),A_262) = k2_xboole_0(B_261,A_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_7450])).

tff(c_2310,plain,(
    ! [A_124,C_125] : k5_xboole_0(A_124,k5_xboole_0(A_124,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1717])).

tff(c_5901,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k2_xboole_0(A_183,B_184)) = k4_xboole_0(B_184,A_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_2310])).

tff(c_7726,plain,(
    ! [A_209,B_210] : k5_xboole_0(k2_xboole_0(A_209,B_210),k4_xboole_0(B_210,A_209)) = A_209 ),
    inference(superposition,[status(thm),theory(equality)],[c_5901,c_2590])).

tff(c_7756,plain,(
    ! [B_210,A_209] : k5_xboole_0(k4_xboole_0(B_210,A_209),A_209) = k2_xboole_0(A_209,B_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_7726,c_2590])).

tff(c_12458,plain,(
    ! [B_261,A_262] : k2_xboole_0(B_261,A_262) = k2_xboole_0(A_262,B_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_12445,c_7756])).

tff(c_38,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12668,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12458,c_38])).

tff(c_12669,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12458,c_14,c_12668])).

tff(c_12867,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_12669])).

tff(c_12871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:50:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.12/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/3.08  
% 8.12/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/3.09  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.12/3.09  
% 8.12/3.09  %Foreground sorts:
% 8.12/3.09  
% 8.12/3.09  
% 8.12/3.09  %Background operators:
% 8.12/3.09  
% 8.12/3.09  
% 8.12/3.09  %Foreground operators:
% 8.12/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.12/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.12/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.12/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.12/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.12/3.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.12/3.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.12/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.12/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.12/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.12/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.12/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.12/3.09  tff('#skF_1', type, '#skF_1': $i).
% 8.12/3.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.12/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.12/3.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.12/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.12/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.12/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.12/3.09  
% 8.24/3.11  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 8.24/3.11  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.24/3.11  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.24/3.11  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.24/3.11  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.24/3.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.24/3.11  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.24/3.11  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.24/3.11  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.24/3.11  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.24/3.11  tff(f_63, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 8.24/3.11  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.24/3.11  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.24/3.11  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/3.11  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.24/3.11  tff(c_126, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.24/3.11  tff(c_508, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), B_79)=k1_xboole_0 | ~r2_hidden(A_78, B_79))), inference(resolution, [status(thm)], [c_32, c_126])).
% 8.24/3.11  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.24/3.11  tff(c_517, plain, (![B_79, A_78]: (k2_xboole_0(B_79, k1_tarski(A_78))=k2_xboole_0(B_79, k1_xboole_0) | ~r2_hidden(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_508, c_14])).
% 8.24/3.11  tff(c_537, plain, (![B_79, A_78]: (k2_xboole_0(B_79, k1_tarski(A_78))=B_79 | ~r2_hidden(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_517])).
% 8.24/3.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.24/3.11  tff(c_230, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.24/3.11  tff(c_242, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_230])).
% 8.24/3.11  tff(c_629, plain, (![A_84, B_85]: (k5_xboole_0(k5_xboole_0(A_84, B_85), k3_xboole_0(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.24/3.11  tff(c_18, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.24/3.11  tff(c_641, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k5_xboole_0(B_85, k3_xboole_0(A_84, B_85)))=k2_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_629, c_18])).
% 8.24/3.11  tff(c_684, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_641])).
% 8.24/3.11  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.24/3.11  tff(c_36, plain, (![A_32]: (r1_tarski(A_32, k1_zfmisc_1(k3_tarski(A_32))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.24/3.11  tff(c_138, plain, (![A_32]: (k4_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_126])).
% 8.24/3.11  tff(c_102, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.24/3.11  tff(c_106, plain, (![A_32]: (k3_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=A_32)), inference(resolution, [status(thm)], [c_36, c_102])).
% 8.24/3.11  tff(c_239, plain, (![A_32]: (k4_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=k5_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_106, c_230])).
% 8.24/3.11  tff(c_248, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_239])).
% 8.24/3.11  tff(c_681, plain, (![A_12]: (k5_xboole_0(A_12, k3_xboole_0(A_12, k1_xboole_0))=k2_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_629])).
% 8.24/3.11  tff(c_689, plain, (![A_86]: (k5_xboole_0(A_86, k3_xboole_0(A_86, k1_xboole_0))=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_681])).
% 8.24/3.11  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.24/3.11  tff(c_755, plain, (![A_87]: (k4_xboole_0(A_87, k1_xboole_0)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_689, c_8])).
% 8.24/3.11  tff(c_121, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.24/3.11  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.24/3.11  tff(c_125, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_12])).
% 8.24/3.11  tff(c_972, plain, (![A_95]: (k3_xboole_0(A_95, k1_xboole_0)=A_95 | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_755, c_125])).
% 8.24/3.11  tff(c_1194, plain, (![B_101]: (k3_xboole_0(k1_xboole_0, B_101)=B_101 | k1_xboole_0!=B_101)), inference(superposition, [status(thm), theory('equality')], [c_2, c_972])).
% 8.24/3.11  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.24/3.11  tff(c_1211, plain, (![B_101]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, B_101), B_101)=k2_xboole_0(k1_xboole_0, B_101) | k1_xboole_0!=B_101)), inference(superposition, [status(thm), theory('equality')], [c_1194, c_20])).
% 8.24/3.11  tff(c_1253, plain, (![B_101]: (k2_xboole_0(k1_xboole_0, B_101)=k1_xboole_0 | k1_xboole_0!=B_101)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_248, c_18, c_1211])).
% 8.24/3.11  tff(c_713, plain, (![A_86]: (k4_xboole_0(A_86, k1_xboole_0)=A_86)), inference(superposition, [status(thm), theory('equality')], [c_689, c_8])).
% 8.24/3.11  tff(c_1016, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_641])).
% 8.24/3.11  tff(c_445, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.24/3.11  tff(c_497, plain, (![A_12, C_77]: (k5_xboole_0(A_12, k5_xboole_0(k1_xboole_0, C_77))=k5_xboole_0(A_12, C_77))), inference(superposition, [status(thm), theory('equality')], [c_16, c_445])).
% 8.24/3.11  tff(c_1030, plain, (![A_12, B_97]: (k5_xboole_0(A_12, k4_xboole_0(B_97, k1_xboole_0))=k5_xboole_0(A_12, k2_xboole_0(k1_xboole_0, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_497])).
% 8.24/3.11  tff(c_1370, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k2_xboole_0(k1_xboole_0, B_106))=k5_xboole_0(A_105, B_106))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_1030])).
% 8.24/3.11  tff(c_1405, plain, (![A_105, B_101]: (k5_xboole_0(A_105, k1_xboole_0)=k5_xboole_0(A_105, B_101) | k1_xboole_0!=B_101)), inference(superposition, [status(thm), theory('equality')], [c_1253, c_1370])).
% 8.24/3.11  tff(c_1443, plain, (![A_105]: (k5_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1405])).
% 8.24/3.11  tff(c_2606, plain, (![A_134, B_135, C_136]: (k5_xboole_0(A_134, k5_xboole_0(k3_xboole_0(A_134, B_135), C_136))=k5_xboole_0(k4_xboole_0(A_134, B_135), C_136))), inference(superposition, [status(thm), theory('equality')], [c_8, c_445])).
% 8.24/3.11  tff(c_2709, plain, (![A_134, B_135]: (k5_xboole_0(k4_xboole_0(A_134, B_135), k3_xboole_0(A_134, B_135))=k5_xboole_0(A_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_248, c_2606])).
% 8.24/3.11  tff(c_4670, plain, (![A_165, B_166]: (k5_xboole_0(k4_xboole_0(A_165, B_166), k3_xboole_0(A_165, B_166))=A_165)), inference(demodulation, [status(thm), theory('equality')], [c_1443, c_2709])).
% 8.24/3.11  tff(c_5596, plain, (![A_179, B_180]: (k5_xboole_0(k4_xboole_0(A_179, B_180), k3_xboole_0(B_180, A_179))=A_179)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4670])).
% 8.24/3.11  tff(c_2484, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k5_xboole_0(B_133, k5_xboole_0(A_132, B_133)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_445, c_248])).
% 8.24/3.11  tff(c_1043, plain, (![A_86]: (k5_xboole_0(k1_xboole_0, A_86)=k2_xboole_0(k1_xboole_0, A_86))), inference(superposition, [status(thm), theory('equality')], [c_713, c_1016])).
% 8.24/3.11  tff(c_483, plain, (![A_32, C_77]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_248, c_445])).
% 8.24/3.11  tff(c_1718, plain, (![A_113, C_114]: (k5_xboole_0(A_113, k5_xboole_0(A_113, C_114))=k2_xboole_0(k1_xboole_0, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_1043, c_483])).
% 8.24/3.11  tff(c_1792, plain, (![A_32]: (k5_xboole_0(A_32, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_248, c_1718])).
% 8.24/3.11  tff(c_1810, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_1443, c_1792])).
% 8.24/3.11  tff(c_1717, plain, (![A_32, C_77]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_77))=k2_xboole_0(k1_xboole_0, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_1043, c_483])).
% 8.24/3.11  tff(c_1811, plain, (![A_32, C_77]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1717])).
% 8.24/3.11  tff(c_2495, plain, (![B_133, A_132]: (k5_xboole_0(B_133, k5_xboole_0(A_132, B_133))=k5_xboole_0(A_132, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2484, c_1811])).
% 8.24/3.11  tff(c_2590, plain, (![B_133, A_132]: (k5_xboole_0(B_133, k5_xboole_0(A_132, B_133))=A_132)), inference(demodulation, [status(thm), theory('equality')], [c_1443, c_2495])).
% 8.24/3.11  tff(c_7396, plain, (![B_205, A_206]: (k5_xboole_0(k3_xboole_0(B_205, A_206), A_206)=k4_xboole_0(A_206, B_205))), inference(superposition, [status(thm), theory('equality')], [c_5596, c_2590])).
% 8.24/3.11  tff(c_490, plain, (![A_5, B_6, C_77]: (k5_xboole_0(A_5, k5_xboole_0(k3_xboole_0(A_5, B_6), C_77))=k5_xboole_0(k4_xboole_0(A_5, B_6), C_77))), inference(superposition, [status(thm), theory('equality')], [c_8, c_445])).
% 8.24/3.11  tff(c_7450, plain, (![B_205, A_206]: (k5_xboole_0(k4_xboole_0(B_205, A_206), A_206)=k5_xboole_0(B_205, k4_xboole_0(A_206, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_7396, c_490])).
% 8.24/3.11  tff(c_12445, plain, (![B_261, A_262]: (k5_xboole_0(k4_xboole_0(B_261, A_262), A_262)=k2_xboole_0(B_261, A_262))), inference(demodulation, [status(thm), theory('equality')], [c_684, c_7450])).
% 8.24/3.11  tff(c_2310, plain, (![A_124, C_125]: (k5_xboole_0(A_124, k5_xboole_0(A_124, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1717])).
% 8.24/3.11  tff(c_5901, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k2_xboole_0(A_183, B_184))=k4_xboole_0(B_184, A_183))), inference(superposition, [status(thm), theory('equality')], [c_684, c_2310])).
% 8.24/3.11  tff(c_7726, plain, (![A_209, B_210]: (k5_xboole_0(k2_xboole_0(A_209, B_210), k4_xboole_0(B_210, A_209))=A_209)), inference(superposition, [status(thm), theory('equality')], [c_5901, c_2590])).
% 8.24/3.11  tff(c_7756, plain, (![B_210, A_209]: (k5_xboole_0(k4_xboole_0(B_210, A_209), A_209)=k2_xboole_0(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_7726, c_2590])).
% 8.24/3.11  tff(c_12458, plain, (![B_261, A_262]: (k2_xboole_0(B_261, A_262)=k2_xboole_0(A_262, B_261))), inference(superposition, [status(thm), theory('equality')], [c_12445, c_7756])).
% 8.24/3.11  tff(c_38, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.24/3.11  tff(c_12668, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12458, c_38])).
% 8.24/3.11  tff(c_12669, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12458, c_14, c_12668])).
% 8.24/3.11  tff(c_12867, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_537, c_12669])).
% 8.24/3.11  tff(c_12871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_12867])).
% 8.24/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/3.11  
% 8.24/3.11  Inference rules
% 8.24/3.11  ----------------------
% 8.24/3.11  #Ref     : 2
% 8.24/3.11  #Sup     : 3264
% 8.24/3.11  #Fact    : 0
% 8.24/3.11  #Define  : 0
% 8.24/3.11  #Split   : 4
% 8.24/3.11  #Chain   : 0
% 8.24/3.11  #Close   : 0
% 8.24/3.11  
% 8.24/3.11  Ordering : KBO
% 8.24/3.11  
% 8.24/3.11  Simplification rules
% 8.24/3.11  ----------------------
% 8.24/3.11  #Subsume      : 394
% 8.24/3.11  #Demod        : 2965
% 8.24/3.11  #Tautology    : 1336
% 8.24/3.11  #SimpNegUnit  : 0
% 8.24/3.11  #BackRed      : 14
% 8.24/3.11  
% 8.24/3.11  #Partial instantiations: 0
% 8.24/3.11  #Strategies tried      : 1
% 8.24/3.11  
% 8.24/3.11  Timing (in seconds)
% 8.24/3.11  ----------------------
% 8.24/3.11  Preprocessing        : 0.31
% 8.24/3.11  Parsing              : 0.17
% 8.24/3.11  CNF conversion       : 0.02
% 8.24/3.11  Main loop            : 2.02
% 8.24/3.11  Inferencing          : 0.49
% 8.24/3.11  Reduction            : 1.04
% 8.24/3.11  Demodulation         : 0.89
% 8.24/3.11  BG Simplification    : 0.07
% 8.24/3.11  Subsumption          : 0.29
% 8.24/3.11  Abstraction          : 0.11
% 8.24/3.11  MUC search           : 0.00
% 8.24/3.11  Cooper               : 0.00
% 8.24/3.11  Total                : 2.37
% 8.24/3.11  Index Insertion      : 0.00
% 8.24/3.11  Index Deletion       : 0.00
% 8.24/3.11  Index Matching       : 0.00
% 8.24/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
