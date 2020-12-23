%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 247 expanded)
%              Number of leaves         :   26 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 303 expanded)
%              Number of equality atoms :   54 ( 181 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_92,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_28])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_312,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_348,plain,(
    ! [A_49,B_50] :
      ( ~ r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_352,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_348])).

tff(c_26,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_359,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_26])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_173,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_194,plain,(
    ! [A_17] : k2_xboole_0(k3_xboole_0(A_17,k1_xboole_0),A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_173])).

tff(c_202,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_194])).

tff(c_368,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_202])).

tff(c_438,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_474,plain,(
    ! [C_55] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_55)) = k4_xboole_0('#skF_3',C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_438])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_110])).

tff(c_132,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_128])).

tff(c_454,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k4_xboole_0(A_53,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_132])).

tff(c_510,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(B_57,A_56)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_454])).

tff(c_711,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_510])).

tff(c_729,plain,(
    ! [A_61,B_62] : k2_xboole_0(k2_xboole_0(A_61,B_62),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_61,B_62),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_18])).

tff(c_776,plain,(
    ! [A_61,B_62] : k2_xboole_0(k2_xboole_0(A_61,B_62),A_61) = k2_xboole_0(A_61,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_2,c_729])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_322,plain,(
    ! [A_14,C_45] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_312])).

tff(c_324,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_501,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,A_53)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_454])).

tff(c_447,plain,(
    ! [C_55,A_53,B_54] : k2_xboole_0(C_55,k4_xboole_0(A_53,k2_xboole_0(B_54,C_55))) = k2_xboole_0(C_55,k4_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_18])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_461,plain,(
    ! [A_53,B_54,B_22] : k4_xboole_0(A_53,k2_xboole_0(B_54,k4_xboole_0(k4_xboole_0(A_53,B_54),B_22))) = k3_xboole_0(k4_xboole_0(A_53,B_54),B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_24])).

tff(c_5184,plain,(
    ! [A_134,B_135,B_136] : k4_xboole_0(A_134,k2_xboole_0(B_135,k4_xboole_0(A_134,k2_xboole_0(B_135,B_136)))) = k3_xboole_0(k4_xboole_0(A_134,B_135),B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_461])).

tff(c_5332,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k4_xboole_0(A_53,B_54))) = k3_xboole_0(k4_xboole_0(A_53,B_54),B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_5184])).

tff(c_5497,plain,(
    ! [A_137,B_138] : k3_xboole_0(k4_xboole_0(A_137,B_138),B_138) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_18,c_5332])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5524,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_137,B_138),B_138),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_137,B_138),B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5497,c_6])).

tff(c_5647,plain,(
    ! [A_139,B_140] : r1_xboole_0(k4_xboole_0(A_139,B_140),B_140) ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_5524])).

tff(c_5920,plain,(
    ! [A_142,B_143,C_144] : r1_xboole_0(k4_xboole_0(A_142,k2_xboole_0(B_143,C_144)),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5647])).

tff(c_6428,plain,(
    ! [A_151,A_152,B_153] : r1_xboole_0(k4_xboole_0(A_151,k2_xboole_0(A_152,B_153)),A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_5920])).

tff(c_6485,plain,(
    ! [C_55] : r1_xboole_0(k4_xboole_0('#skF_3',C_55),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_6428])).

tff(c_204,plain,(
    ! [A_41] : k2_xboole_0(k1_xboole_0,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_194])).

tff(c_228,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_97,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_2724,plain,(
    ! [C_106,A_107,B_108] : k2_xboole_0(C_106,k4_xboole_0(A_107,k2_xboole_0(B_108,C_106))) = k2_xboole_0(C_106,k4_xboole_0(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_18])).

tff(c_2864,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2724])).

tff(c_2907,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_2864])).

tff(c_528,plain,(
    ! [A_56,B_57] : k3_xboole_0(A_56,k2_xboole_0(B_57,A_56)) = k4_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_24])).

tff(c_986,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k2_xboole_0(B_71,A_70)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_528])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_999,plain,(
    ! [A_70,B_71,C_9] :
      ( ~ r1_xboole_0(A_70,k2_xboole_0(B_71,A_70))
      | ~ r2_hidden(C_9,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_8])).

tff(c_2914,plain,(
    ! [C_9] :
      ( ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5')
      | ~ r2_hidden(C_9,k4_xboole_0('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2907,c_999])).

tff(c_3844,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2914])).

tff(c_6592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_3844])).

tff(c_6595,plain,(
    ! [C_154] : ~ r2_hidden(C_154,k4_xboole_0('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2914])).

tff(c_6603,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_6595])).

tff(c_6608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_6603])).

tff(c_6609,plain,(
    ! [A_14] : ~ r1_xboole_0(A_14,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_6627,plain,(
    ! [A_158,B_159] :
      ( ~ r1_xboole_0(A_158,B_159)
      | k3_xboole_0(A_158,B_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_6631,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_6627])).

tff(c_6635,plain,(
    ! [C_9] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6631,c_8])).

tff(c_6642,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6635])).

tff(c_7073,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173,B_174),k3_xboole_0(A_173,B_174))
      | r1_xboole_0(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7091,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7073])).

tff(c_7098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6609,c_6642,c_7091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.07  
% 5.26/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.26/2.07  
% 5.26/2.07  %Foreground sorts:
% 5.26/2.07  
% 5.26/2.07  
% 5.26/2.07  %Background operators:
% 5.26/2.07  
% 5.26/2.07  
% 5.26/2.07  %Foreground operators:
% 5.26/2.07  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.26/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.26/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.26/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.26/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.26/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.26/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.26/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.26/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.26/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.26/2.07  
% 5.26/2.09  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.26/2.09  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.26/2.09  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.26/2.09  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.26/2.09  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.26/2.09  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.26/2.09  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.26/2.09  tff(f_63, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.26/2.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.26/2.09  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.26/2.09  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.26/2.09  tff(c_92, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.26/2.09  tff(c_28, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.09  tff(c_96, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_28])).
% 5.26/2.09  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.26/2.09  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.09  tff(c_312, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.09  tff(c_348, plain, (![A_49, B_50]: (~r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_312])).
% 5.26/2.09  tff(c_352, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_348])).
% 5.26/2.09  tff(c_26, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.26/2.09  tff(c_359, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_352, c_26])).
% 5.26/2.09  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.26/2.09  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.26/2.09  tff(c_173, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.26/2.09  tff(c_194, plain, (![A_17]: (k2_xboole_0(k3_xboole_0(A_17, k1_xboole_0), A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_20, c_173])).
% 5.26/2.09  tff(c_202, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_194])).
% 5.26/2.09  tff(c_368, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_359, c_202])).
% 5.26/2.09  tff(c_438, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.26/2.09  tff(c_474, plain, (![C_55]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_55))=k4_xboole_0('#skF_3', C_55))), inference(superposition, [status(thm), theory('equality')], [c_368, c_438])).
% 5.26/2.09  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.09  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.26/2.09  tff(c_110, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.26/2.09  tff(c_128, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_110])).
% 5.26/2.09  tff(c_132, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_128])).
% 5.26/2.09  tff(c_454, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k4_xboole_0(A_53, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_438, c_132])).
% 5.26/2.09  tff(c_510, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(B_57, A_56))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_454])).
% 5.26/2.09  tff(c_711, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k2_xboole_0(A_61, B_62))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_510])).
% 5.26/2.09  tff(c_729, plain, (![A_61, B_62]: (k2_xboole_0(k2_xboole_0(A_61, B_62), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_61, B_62), A_61))), inference(superposition, [status(thm), theory('equality')], [c_711, c_18])).
% 5.26/2.09  tff(c_776, plain, (![A_61, B_62]: (k2_xboole_0(k2_xboole_0(A_61, B_62), A_61)=k2_xboole_0(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_2, c_729])).
% 5.26/2.09  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.26/2.09  tff(c_322, plain, (![A_14, C_45]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_312])).
% 5.26/2.09  tff(c_324, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_322])).
% 5.26/2.09  tff(c_501, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, A_53))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_454])).
% 5.26/2.09  tff(c_447, plain, (![C_55, A_53, B_54]: (k2_xboole_0(C_55, k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))=k2_xboole_0(C_55, k4_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_438, c_18])).
% 5.26/2.09  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.26/2.09  tff(c_461, plain, (![A_53, B_54, B_22]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k4_xboole_0(k4_xboole_0(A_53, B_54), B_22)))=k3_xboole_0(k4_xboole_0(A_53, B_54), B_22))), inference(superposition, [status(thm), theory('equality')], [c_438, c_24])).
% 5.26/2.09  tff(c_5184, plain, (![A_134, B_135, B_136]: (k4_xboole_0(A_134, k2_xboole_0(B_135, k4_xboole_0(A_134, k2_xboole_0(B_135, B_136))))=k3_xboole_0(k4_xboole_0(A_134, B_135), B_136))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_461])).
% 5.26/2.09  tff(c_5332, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k4_xboole_0(A_53, B_54)))=k3_xboole_0(k4_xboole_0(A_53, B_54), B_54))), inference(superposition, [status(thm), theory('equality')], [c_447, c_5184])).
% 5.26/2.09  tff(c_5497, plain, (![A_137, B_138]: (k3_xboole_0(k4_xboole_0(A_137, B_138), B_138)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_501, c_18, c_5332])).
% 5.26/2.09  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.09  tff(c_5524, plain, (![A_137, B_138]: (r2_hidden('#skF_1'(k4_xboole_0(A_137, B_138), B_138), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_137, B_138), B_138))), inference(superposition, [status(thm), theory('equality')], [c_5497, c_6])).
% 5.26/2.09  tff(c_5647, plain, (![A_139, B_140]: (r1_xboole_0(k4_xboole_0(A_139, B_140), B_140))), inference(negUnitSimplification, [status(thm)], [c_324, c_5524])).
% 5.26/2.09  tff(c_5920, plain, (![A_142, B_143, C_144]: (r1_xboole_0(k4_xboole_0(A_142, k2_xboole_0(B_143, C_144)), C_144))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5647])).
% 5.26/2.09  tff(c_6428, plain, (![A_151, A_152, B_153]: (r1_xboole_0(k4_xboole_0(A_151, k2_xboole_0(A_152, B_153)), A_152))), inference(superposition, [status(thm), theory('equality')], [c_776, c_5920])).
% 5.26/2.09  tff(c_6485, plain, (![C_55]: (r1_xboole_0(k4_xboole_0('#skF_3', C_55), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_474, c_6428])).
% 5.26/2.09  tff(c_204, plain, (![A_41]: (k2_xboole_0(k1_xboole_0, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_194])).
% 5.26/2.09  tff(c_228, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 5.26/2.09  tff(c_32, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.09  tff(c_97, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.26/2.09  tff(c_105, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_97])).
% 5.26/2.09  tff(c_2724, plain, (![C_106, A_107, B_108]: (k2_xboole_0(C_106, k4_xboole_0(A_107, k2_xboole_0(B_108, C_106)))=k2_xboole_0(C_106, k4_xboole_0(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_438, c_18])).
% 5.26/2.09  tff(c_2864, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_2724])).
% 5.26/2.09  tff(c_2907, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_2864])).
% 5.26/2.09  tff(c_528, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k2_xboole_0(B_57, A_56))=k4_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_510, c_24])).
% 5.26/2.09  tff(c_986, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k2_xboole_0(B_71, A_70))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_528])).
% 5.26/2.09  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.09  tff(c_999, plain, (![A_70, B_71, C_9]: (~r1_xboole_0(A_70, k2_xboole_0(B_71, A_70)) | ~r2_hidden(C_9, A_70))), inference(superposition, [status(thm), theory('equality')], [c_986, c_8])).
% 5.26/2.09  tff(c_2914, plain, (![C_9]: (~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden(C_9, k4_xboole_0('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2907, c_999])).
% 5.26/2.09  tff(c_3844, plain, (~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2914])).
% 5.26/2.09  tff(c_6592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6485, c_3844])).
% 5.26/2.09  tff(c_6595, plain, (![C_154]: (~r2_hidden(C_154, k4_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_2914])).
% 5.26/2.09  tff(c_6603, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_6595])).
% 5.26/2.09  tff(c_6608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_6603])).
% 5.26/2.09  tff(c_6609, plain, (![A_14]: (~r1_xboole_0(A_14, k1_xboole_0))), inference(splitRight, [status(thm)], [c_322])).
% 5.26/2.09  tff(c_6627, plain, (![A_158, B_159]: (~r1_xboole_0(A_158, B_159) | k3_xboole_0(A_158, B_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_312])).
% 5.26/2.09  tff(c_6631, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_6627])).
% 5.26/2.09  tff(c_6635, plain, (![C_9]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6631, c_8])).
% 5.26/2.09  tff(c_6642, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6635])).
% 5.26/2.09  tff(c_7073, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173, B_174), k3_xboole_0(A_173, B_174)) | r1_xboole_0(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.09  tff(c_7091, plain, (![A_14]: (r2_hidden('#skF_1'(A_14, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7073])).
% 5.26/2.09  tff(c_7098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6609, c_6642, c_7091])).
% 5.26/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.09  
% 5.26/2.09  Inference rules
% 5.26/2.09  ----------------------
% 5.26/2.09  #Ref     : 0
% 5.26/2.09  #Sup     : 1774
% 5.26/2.09  #Fact    : 0
% 5.26/2.09  #Define  : 0
% 5.26/2.09  #Split   : 5
% 5.26/2.09  #Chain   : 0
% 5.26/2.09  #Close   : 0
% 5.26/2.09  
% 5.26/2.09  Ordering : KBO
% 5.26/2.09  
% 5.26/2.09  Simplification rules
% 5.26/2.09  ----------------------
% 5.26/2.09  #Subsume      : 24
% 5.26/2.09  #Demod        : 1845
% 5.26/2.09  #Tautology    : 1217
% 5.26/2.09  #SimpNegUnit  : 13
% 5.26/2.09  #BackRed      : 5
% 5.26/2.09  
% 5.26/2.09  #Partial instantiations: 0
% 5.26/2.09  #Strategies tried      : 1
% 5.26/2.09  
% 5.26/2.09  Timing (in seconds)
% 5.26/2.09  ----------------------
% 5.26/2.09  Preprocessing        : 0.27
% 5.26/2.09  Parsing              : 0.15
% 5.26/2.09  CNF conversion       : 0.02
% 5.26/2.09  Main loop            : 1.05
% 5.26/2.09  Inferencing          : 0.31
% 5.26/2.09  Reduction            : 0.50
% 5.26/2.09  Demodulation         : 0.42
% 5.26/2.09  BG Simplification    : 0.03
% 5.26/2.09  Subsumption          : 0.13
% 5.26/2.10  Abstraction          : 0.05
% 5.26/2.10  MUC search           : 0.00
% 5.26/2.10  Cooper               : 0.00
% 5.26/2.10  Total                : 1.36
% 5.26/2.10  Index Insertion      : 0.00
% 5.26/2.10  Index Deletion       : 0.00
% 5.26/2.10  Index Matching       : 0.00
% 5.26/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
