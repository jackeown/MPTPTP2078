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
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 14.66s
% Output     : CNFRefutation 14.66s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 185 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 284 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_83,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_89,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_93,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_45])).

tff(c_24,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),B_32) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_32,A_31] : r1_xboole_0(B_32,k4_xboole_0(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150,plain,(
    ! [A_52,B_53] :
      ( ~ r1_xboole_0(A_52,B_53)
      | k3_xboole_0(A_52,B_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_165,plain,(
    ! [B_32,A_31] : k3_xboole_0(B_32,k4_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_150])).

tff(c_222,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_234,plain,(
    ! [B_32,A_31] : k4_xboole_0(B_32,k4_xboole_0(A_31,B_32)) = k5_xboole_0(B_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_222])).

tff(c_247,plain,(
    ! [B_32,A_31] : k4_xboole_0(B_32,k4_xboole_0(A_31,B_32)) = B_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_234])).

tff(c_167,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,k4_xboole_0(A_55,B_54)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_150])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    ! [B_54,A_55,C_9] :
      ( ~ r1_xboole_0(B_54,k4_xboole_0(A_55,B_54))
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_180,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_172])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_910,plain,(
    ! [A_83,B_84,C_85] : k4_xboole_0(k3_xboole_0(A_83,B_84),C_85) = k3_xboole_0(A_83,k4_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1416,plain,(
    ! [A_95,B_96,C_97] : r1_xboole_0(k3_xboole_0(A_95,k4_xboole_0(B_96,C_97)),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_30])).

tff(c_1477,plain,(
    ! [B_96,C_97,B_2] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_96,C_97),B_2),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1416])).

tff(c_3728,plain,(
    ! [A_145,B_146,C_147] :
      ( ~ r1_xboole_0(A_145,B_146)
      | ~ r2_hidden(C_147,k3_xboole_0(B_146,A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_3960,plain,(
    ! [A_151,B_152] :
      ( ~ r1_xboole_0(A_151,B_152)
      | k3_xboole_0(B_152,A_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_3728])).

tff(c_24463,plain,(
    ! [C_393,B_394,B_395] : k3_xboole_0(C_393,k3_xboole_0(k4_xboole_0(B_394,C_393),B_395)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1477,c_3960])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k4_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_699,plain,(
    ! [A_77,B_78,C_79] : k3_xboole_0(k3_xboole_0(A_77,B_78),C_79) = k3_xboole_0(A_77,k3_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_715,plain,(
    ! [A_77,B_78,C_79] : k5_xboole_0(k3_xboole_0(A_77,B_78),k3_xboole_0(A_77,k3_xboole_0(B_78,C_79))) = k4_xboole_0(k3_xboole_0(A_77,B_78),C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_16])).

tff(c_12392,plain,(
    ! [A_77,B_78,C_79] : k5_xboole_0(k3_xboole_0(A_77,B_78),k3_xboole_0(A_77,k3_xboole_0(B_78,C_79))) = k3_xboole_0(A_77,k4_xboole_0(B_78,C_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_715])).

tff(c_24578,plain,(
    ! [C_393,B_394,B_395] : k5_xboole_0(k3_xboole_0(C_393,k4_xboole_0(B_394,C_393)),k1_xboole_0) = k3_xboole_0(C_393,k4_xboole_0(k4_xboole_0(B_394,C_393),B_395)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24463,c_12392])).

tff(c_34474,plain,(
    ! [C_452,B_453,B_454] : k3_xboole_0(C_452,k4_xboole_0(k4_xboole_0(B_453,C_452),B_454)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_24,c_24578])).

tff(c_1169,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),k3_xboole_0(A_88,B_89))
      | r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1208,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1169])).

tff(c_34707,plain,(
    ! [B_453,C_452,B_454] :
      ( r2_hidden('#skF_1'(k4_xboole_0(k4_xboole_0(B_453,C_452),B_454),C_452),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(k4_xboole_0(B_453,C_452),B_454),C_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34474,c_1208])).

tff(c_35052,plain,(
    ! [B_455,C_456,B_457] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_455,C_456),B_457),C_456) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_34707])).

tff(c_35338,plain,(
    ! [B_461,B_462,A_463] : r1_xboole_0(k4_xboole_0(B_461,B_462),k4_xboole_0(A_463,B_461)) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_35052])).

tff(c_34,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_94,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k3_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k3_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_352,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | r1_xboole_0(A_63,k3_xboole_0(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1966,plain,(
    ! [B_115,C_116,A_117] :
      ( r1_xboole_0(k3_xboole_0(B_115,C_116),A_117)
      | ~ r1_xboole_0(A_117,B_115) ) ),
    inference(resolution,[status(thm)],[c_352,c_4])).

tff(c_140,plain,(
    ! [A_49,B_50] :
      ( ~ r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_1975,plain,(
    ! [B_115,C_116,A_117] :
      ( k3_xboole_0(k3_xboole_0(B_115,C_116),A_117) = k1_xboole_0
      | ~ r1_xboole_0(A_117,B_115) ) ),
    inference(resolution,[status(thm)],[c_1966,c_140])).

tff(c_16987,plain,(
    ! [B_346,C_347,A_348] :
      ( k3_xboole_0(B_346,k3_xboole_0(C_347,A_348)) = k1_xboole_0
      | ~ r1_xboole_0(A_348,B_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1975])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17305,plain,(
    ! [B_346,C_347,A_348] :
      ( r2_hidden('#skF_1'(B_346,k3_xboole_0(C_347,A_348)),k1_xboole_0)
      | r1_xboole_0(B_346,k3_xboole_0(C_347,A_348))
      | ~ r1_xboole_0(A_348,B_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16987,c_6])).

tff(c_25133,plain,(
    ! [B_396,C_397,A_398] :
      ( r1_xboole_0(B_396,k3_xboole_0(C_397,A_398))
      | ~ r1_xboole_0(A_398,B_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_17305])).

tff(c_25286,plain,(
    ! [B_396] :
      ( r1_xboole_0(B_396,'#skF_3')
      | ~ r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),B_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_25133])).

tff(c_35542,plain,(
    ! [A_464] : r1_xboole_0(k4_xboole_0(A_464,'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_35338,c_25286])).

tff(c_3845,plain,(
    ! [A_145,B_146] :
      ( ~ r1_xboole_0(A_145,B_146)
      | k3_xboole_0(B_146,A_145) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_3728])).

tff(c_36002,plain,(
    ! [A_467] : k3_xboole_0('#skF_3',k4_xboole_0(A_467,'#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35542,c_3845])).

tff(c_971,plain,(
    ! [C_85] : k3_xboole_0('#skF_3',k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_85)) = k4_xboole_0('#skF_3',C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_910])).

tff(c_36226,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36002,c_971])).

tff(c_36364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_36226])).

tff(c_36365,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36429,plain,(
    ! [A_477,B_478] :
      ( k3_xboole_0(A_477,B_478) = A_477
      | ~ r1_tarski(A_477,B_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36437,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_36429])).

tff(c_36768,plain,(
    ! [A_503,B_504,C_505] : k4_xboole_0(k3_xboole_0(A_503,B_504),C_505) = k3_xboole_0(A_503,k4_xboole_0(B_504,C_505)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37156,plain,(
    ! [A_517,B_518,C_519] : r1_xboole_0(k3_xboole_0(A_517,k4_xboole_0(B_518,C_519)),C_519) ),
    inference(superposition,[status(thm),theory(equality)],[c_36768,c_30])).

tff(c_37185,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36437,c_37156])).

tff(c_37206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36365,c_37185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.66/6.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.92  
% 14.66/6.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 14.66/6.92  
% 14.66/6.92  %Foreground sorts:
% 14.66/6.92  
% 14.66/6.92  
% 14.66/6.92  %Background operators:
% 14.66/6.92  
% 14.66/6.92  
% 14.66/6.92  %Foreground operators:
% 14.66/6.92  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.66/6.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.66/6.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.66/6.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.66/6.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.66/6.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.66/6.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.66/6.92  tff('#skF_5', type, '#skF_5': $i).
% 14.66/6.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.66/6.92  tff('#skF_3', type, '#skF_3': $i).
% 14.66/6.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.66/6.92  tff('#skF_4', type, '#skF_4': $i).
% 14.66/6.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.66/6.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.66/6.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.66/6.92  
% 14.66/6.94  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.66/6.94  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 14.66/6.94  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 14.66/6.94  tff(f_83, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 14.66/6.94  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.66/6.94  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.66/6.94  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.66/6.94  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.66/6.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.66/6.94  tff(f_67, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 14.66/6.94  tff(f_61, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 14.66/6.94  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.66/6.94  tff(f_81, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 14.66/6.94  tff(c_89, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.66/6.94  tff(c_32, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.66/6.94  tff(c_45, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 14.66/6.94  tff(c_93, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_45])).
% 14.66/6.94  tff(c_24, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.66/6.94  tff(c_30, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), B_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.66/6.94  tff(c_80, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.66/6.94  tff(c_83, plain, (![B_32, A_31]: (r1_xboole_0(B_32, k4_xboole_0(A_31, B_32)))), inference(resolution, [status(thm)], [c_30, c_80])).
% 14.66/6.94  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.66/6.94  tff(c_126, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.66/6.94  tff(c_150, plain, (![A_52, B_53]: (~r1_xboole_0(A_52, B_53) | k3_xboole_0(A_52, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_126])).
% 14.66/6.94  tff(c_165, plain, (![B_32, A_31]: (k3_xboole_0(B_32, k4_xboole_0(A_31, B_32))=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_150])).
% 14.66/6.94  tff(c_222, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.66/6.94  tff(c_234, plain, (![B_32, A_31]: (k4_xboole_0(B_32, k4_xboole_0(A_31, B_32))=k5_xboole_0(B_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_222])).
% 14.66/6.94  tff(c_247, plain, (![B_32, A_31]: (k4_xboole_0(B_32, k4_xboole_0(A_31, B_32))=B_32)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_234])).
% 14.66/6.94  tff(c_167, plain, (![B_54, A_55]: (k3_xboole_0(B_54, k4_xboole_0(A_55, B_54))=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_150])).
% 14.66/6.94  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.66/6.94  tff(c_172, plain, (![B_54, A_55, C_9]: (~r1_xboole_0(B_54, k4_xboole_0(A_55, B_54)) | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 14.66/6.94  tff(c_180, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_172])).
% 14.66/6.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.66/6.94  tff(c_910, plain, (![A_83, B_84, C_85]: (k4_xboole_0(k3_xboole_0(A_83, B_84), C_85)=k3_xboole_0(A_83, k4_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.66/6.94  tff(c_1416, plain, (![A_95, B_96, C_97]: (r1_xboole_0(k3_xboole_0(A_95, k4_xboole_0(B_96, C_97)), C_97))), inference(superposition, [status(thm), theory('equality')], [c_910, c_30])).
% 14.66/6.94  tff(c_1477, plain, (![B_96, C_97, B_2]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_96, C_97), B_2), C_97))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1416])).
% 14.66/6.94  tff(c_3728, plain, (![A_145, B_146, C_147]: (~r1_xboole_0(A_145, B_146) | ~r2_hidden(C_147, k3_xboole_0(B_146, A_145)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 14.66/6.94  tff(c_3960, plain, (![A_151, B_152]: (~r1_xboole_0(A_151, B_152) | k3_xboole_0(B_152, A_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_3728])).
% 14.66/6.94  tff(c_24463, plain, (![C_393, B_394, B_395]: (k3_xboole_0(C_393, k3_xboole_0(k4_xboole_0(B_394, C_393), B_395))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1477, c_3960])).
% 14.66/6.94  tff(c_22, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.66/6.94  tff(c_699, plain, (![A_77, B_78, C_79]: (k3_xboole_0(k3_xboole_0(A_77, B_78), C_79)=k3_xboole_0(A_77, k3_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.66/6.94  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.66/6.94  tff(c_715, plain, (![A_77, B_78, C_79]: (k5_xboole_0(k3_xboole_0(A_77, B_78), k3_xboole_0(A_77, k3_xboole_0(B_78, C_79)))=k4_xboole_0(k3_xboole_0(A_77, B_78), C_79))), inference(superposition, [status(thm), theory('equality')], [c_699, c_16])).
% 14.66/6.94  tff(c_12392, plain, (![A_77, B_78, C_79]: (k5_xboole_0(k3_xboole_0(A_77, B_78), k3_xboole_0(A_77, k3_xboole_0(B_78, C_79)))=k3_xboole_0(A_77, k4_xboole_0(B_78, C_79)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_715])).
% 14.66/6.94  tff(c_24578, plain, (![C_393, B_394, B_395]: (k5_xboole_0(k3_xboole_0(C_393, k4_xboole_0(B_394, C_393)), k1_xboole_0)=k3_xboole_0(C_393, k4_xboole_0(k4_xboole_0(B_394, C_393), B_395)))), inference(superposition, [status(thm), theory('equality')], [c_24463, c_12392])).
% 14.66/6.94  tff(c_34474, plain, (![C_452, B_453, B_454]: (k3_xboole_0(C_452, k4_xboole_0(k4_xboole_0(B_453, C_452), B_454))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_24, c_24578])).
% 14.66/6.94  tff(c_1169, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), k3_xboole_0(A_88, B_89)) | r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.66/6.94  tff(c_1208, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1169])).
% 14.66/6.94  tff(c_34707, plain, (![B_453, C_452, B_454]: (r2_hidden('#skF_1'(k4_xboole_0(k4_xboole_0(B_453, C_452), B_454), C_452), k1_xboole_0) | r1_xboole_0(k4_xboole_0(k4_xboole_0(B_453, C_452), B_454), C_452))), inference(superposition, [status(thm), theory('equality')], [c_34474, c_1208])).
% 14.66/6.94  tff(c_35052, plain, (![B_455, C_456, B_457]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_455, C_456), B_457), C_456))), inference(negUnitSimplification, [status(thm)], [c_180, c_34707])).
% 14.66/6.94  tff(c_35338, plain, (![B_461, B_462, A_463]: (r1_xboole_0(k4_xboole_0(B_461, B_462), k4_xboole_0(A_463, B_461)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_35052])).
% 14.66/6.94  tff(c_34, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.66/6.94  tff(c_94, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.66/6.94  tff(c_102, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_94])).
% 14.66/6.94  tff(c_18, plain, (![A_16, B_17, C_18]: (k3_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k3_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.66/6.94  tff(c_352, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | r1_xboole_0(A_63, k3_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.66/6.94  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.66/6.94  tff(c_1966, plain, (![B_115, C_116, A_117]: (r1_xboole_0(k3_xboole_0(B_115, C_116), A_117) | ~r1_xboole_0(A_117, B_115))), inference(resolution, [status(thm)], [c_352, c_4])).
% 14.66/6.94  tff(c_140, plain, (![A_49, B_50]: (~r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_126])).
% 14.66/6.94  tff(c_1975, plain, (![B_115, C_116, A_117]: (k3_xboole_0(k3_xboole_0(B_115, C_116), A_117)=k1_xboole_0 | ~r1_xboole_0(A_117, B_115))), inference(resolution, [status(thm)], [c_1966, c_140])).
% 14.66/6.94  tff(c_16987, plain, (![B_346, C_347, A_348]: (k3_xboole_0(B_346, k3_xboole_0(C_347, A_348))=k1_xboole_0 | ~r1_xboole_0(A_348, B_346))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1975])).
% 14.66/6.94  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.66/6.94  tff(c_17305, plain, (![B_346, C_347, A_348]: (r2_hidden('#skF_1'(B_346, k3_xboole_0(C_347, A_348)), k1_xboole_0) | r1_xboole_0(B_346, k3_xboole_0(C_347, A_348)) | ~r1_xboole_0(A_348, B_346))), inference(superposition, [status(thm), theory('equality')], [c_16987, c_6])).
% 14.66/6.94  tff(c_25133, plain, (![B_396, C_397, A_398]: (r1_xboole_0(B_396, k3_xboole_0(C_397, A_398)) | ~r1_xboole_0(A_398, B_396))), inference(negUnitSimplification, [status(thm)], [c_180, c_17305])).
% 14.66/6.94  tff(c_25286, plain, (![B_396]: (r1_xboole_0(B_396, '#skF_3') | ~r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), B_396))), inference(superposition, [status(thm), theory('equality')], [c_102, c_25133])).
% 14.66/6.94  tff(c_35542, plain, (![A_464]: (r1_xboole_0(k4_xboole_0(A_464, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_35338, c_25286])).
% 14.66/6.94  tff(c_3845, plain, (![A_145, B_146]: (~r1_xboole_0(A_145, B_146) | k3_xboole_0(B_146, A_145)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_3728])).
% 14.66/6.94  tff(c_36002, plain, (![A_467]: (k3_xboole_0('#skF_3', k4_xboole_0(A_467, '#skF_4'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_35542, c_3845])).
% 14.66/6.94  tff(c_971, plain, (![C_85]: (k3_xboole_0('#skF_3', k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_85))=k4_xboole_0('#skF_3', C_85))), inference(superposition, [status(thm), theory('equality')], [c_102, c_910])).
% 14.66/6.94  tff(c_36226, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36002, c_971])).
% 14.66/6.94  tff(c_36364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_36226])).
% 14.66/6.94  tff(c_36365, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 14.66/6.94  tff(c_36429, plain, (![A_477, B_478]: (k3_xboole_0(A_477, B_478)=A_477 | ~r1_tarski(A_477, B_478))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.66/6.94  tff(c_36437, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_36429])).
% 14.66/6.94  tff(c_36768, plain, (![A_503, B_504, C_505]: (k4_xboole_0(k3_xboole_0(A_503, B_504), C_505)=k3_xboole_0(A_503, k4_xboole_0(B_504, C_505)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.66/6.94  tff(c_37156, plain, (![A_517, B_518, C_519]: (r1_xboole_0(k3_xboole_0(A_517, k4_xboole_0(B_518, C_519)), C_519))), inference(superposition, [status(thm), theory('equality')], [c_36768, c_30])).
% 14.66/6.94  tff(c_37185, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36437, c_37156])).
% 14.66/6.94  tff(c_37206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36365, c_37185])).
% 14.66/6.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.94  
% 14.66/6.94  Inference rules
% 14.66/6.94  ----------------------
% 14.66/6.94  #Ref     : 0
% 14.66/6.94  #Sup     : 9427
% 14.66/6.94  #Fact    : 0
% 14.66/6.94  #Define  : 0
% 14.66/6.94  #Split   : 7
% 14.66/6.94  #Chain   : 0
% 14.66/6.94  #Close   : 0
% 14.66/6.94  
% 14.66/6.94  Ordering : KBO
% 14.66/6.94  
% 14.66/6.94  Simplification rules
% 14.66/6.94  ----------------------
% 14.66/6.94  #Subsume      : 1201
% 14.66/6.94  #Demod        : 7208
% 14.66/6.94  #Tautology    : 4864
% 14.66/6.94  #SimpNegUnit  : 219
% 14.66/6.94  #BackRed      : 2
% 14.66/6.94  
% 14.66/6.94  #Partial instantiations: 0
% 14.66/6.94  #Strategies tried      : 1
% 14.66/6.94  
% 14.66/6.94  Timing (in seconds)
% 14.66/6.94  ----------------------
% 14.66/6.94  Preprocessing        : 0.33
% 14.66/6.94  Parsing              : 0.18
% 14.66/6.94  CNF conversion       : 0.02
% 14.66/6.94  Main loop            : 5.76
% 14.66/6.94  Inferencing          : 0.89
% 14.66/6.94  Reduction            : 3.51
% 14.66/6.94  Demodulation         : 3.12
% 14.66/6.94  BG Simplification    : 0.10
% 14.66/6.94  Subsumption          : 1.02
% 14.66/6.94  Abstraction          : 0.14
% 14.66/6.94  MUC search           : 0.00
% 14.66/6.94  Cooper               : 0.00
% 14.66/6.94  Total                : 6.13
% 14.66/6.94  Index Insertion      : 0.00
% 14.66/6.94  Index Deletion       : 0.00
% 14.66/6.94  Index Matching       : 0.00
% 14.66/6.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
