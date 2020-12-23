%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 22.85s
% Output     : CNFRefutation 23.04s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 343 expanded)
%              Number of leaves         :   29 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :   63 ( 370 expanded)
%              Number of equality atoms :   55 ( 310 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(A_55,B_56)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_177,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_177])).

tff(c_192,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_186])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_151,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_151])).

tff(c_169,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_160])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_272,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2128,plain,(
    ! [A_150,B_151,C_152] : k5_xboole_0(A_150,k5_xboole_0(k4_xboole_0(B_151,A_150),C_152)) = k5_xboole_0(k2_xboole_0(A_150,B_151),C_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_272])).

tff(c_2250,plain,(
    ! [A_150,B_151] : k5_xboole_0(k2_xboole_0(A_150,B_151),k4_xboole_0(B_151,A_150)) = k5_xboole_0(A_150,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2128])).

tff(c_2273,plain,(
    ! [A_153,B_154] : k5_xboole_0(k2_xboole_0(A_153,B_154),k4_xboole_0(B_154,A_153)) = A_153 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_2250])).

tff(c_929,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k5_xboole_0(B_121,k5_xboole_0(A_120,B_121))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_272])).

tff(c_501,plain,(
    ! [B_90,C_91] : k5_xboole_0(B_90,k5_xboole_0(B_90,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_272])).

tff(c_561,plain,(
    ! [B_6] : k5_xboole_0(k1_xboole_0,B_6) = k5_xboole_0(B_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_501])).

tff(c_579,plain,(
    ! [B_6] : k5_xboole_0(k1_xboole_0,B_6) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_561])).

tff(c_328,plain,(
    ! [B_6,C_80] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_272])).

tff(c_580,plain,(
    ! [B_6,C_80] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_80)) = C_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_328])).

tff(c_937,plain,(
    ! [B_121,A_120] : k5_xboole_0(B_121,k5_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_580])).

tff(c_1008,plain,(
    ! [B_121,A_120] : k5_xboole_0(B_121,k5_xboole_0(A_120,B_121)) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_937])).

tff(c_2285,plain,(
    ! [B_154,A_153] : k5_xboole_0(k4_xboole_0(B_154,A_153),A_153) = k2_xboole_0(A_153,B_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_2273,c_1008])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1584,plain,(
    ! [A_138,B_139,C_140] : k5_xboole_0(A_138,k5_xboole_0(k3_xboole_0(A_138,B_139),C_140)) = k5_xboole_0(k4_xboole_0(A_138,B_139),C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_272])).

tff(c_1682,plain,(
    ! [A_138,B_139] : k5_xboole_0(k4_xboole_0(A_138,B_139),k3_xboole_0(A_138,B_139)) = k5_xboole_0(A_138,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_1584])).

tff(c_1708,plain,(
    ! [A_141,B_142] : k5_xboole_0(k4_xboole_0(A_141,B_142),k3_xboole_0(A_141,B_142)) = A_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1682])).

tff(c_1726,plain,(
    ! [A_141,B_142] : k5_xboole_0(k3_xboole_0(A_141,B_142),A_141) = k4_xboole_0(A_141,B_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_1008])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_5367,plain,(
    ! [A_200,B_201,C_202] : k5_xboole_0(A_200,k5_xboole_0(k3_xboole_0(B_201,A_200),C_202)) = k5_xboole_0(k4_xboole_0(A_200,B_201),C_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_272])).

tff(c_5437,plain,(
    ! [B_142,A_141] : k5_xboole_0(k4_xboole_0(B_142,A_141),A_141) = k5_xboole_0(B_142,k4_xboole_0(A_141,B_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1726,c_5367])).

tff(c_5599,plain,(
    ! [B_142,A_141] : k2_xboole_0(B_142,A_141) = k2_xboole_0(A_141,B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_20,c_5437])).

tff(c_36,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_252,plain,(
    ! [A_76,B_77] : k3_xboole_0(k1_tarski(A_76),k2_tarski(A_76,B_77)) = k1_tarski(A_76) ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_261,plain,(
    ! [A_76,B_77] : k5_xboole_0(k1_tarski(A_76),k1_tarski(A_76)) = k4_xboole_0(k1_tarski(A_76),k2_tarski(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_12])).

tff(c_346,plain,(
    ! [A_81,B_82] : k4_xboole_0(k1_tarski(A_81),k2_tarski(A_81,B_82)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_261])).

tff(c_351,plain,(
    ! [A_81,B_82] : k2_xboole_0(k2_tarski(A_81,B_82),k1_tarski(A_81)) = k5_xboole_0(k2_tarski(A_81,B_82),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_20])).

tff(c_49317,plain,(
    ! [A_440,B_441] : k2_xboole_0(k2_tarski(A_440,B_441),k1_tarski(A_440)) = k2_tarski(A_440,B_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_351])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_11,B_12] : k5_xboole_0(k2_xboole_0(A_11,B_12),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_902,plain,(
    ! [A_11,B_12] : k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) = k2_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_189])).

tff(c_49440,plain,(
    ! [A_440,B_441] : k2_xboole_0(k2_tarski(A_440,B_441),k2_tarski(A_440,B_441)) = k2_xboole_0(k2_tarski(A_440,B_441),k1_tarski(A_440)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49317,c_902])).

tff(c_49488,plain,(
    ! [A_440,B_441] : k2_xboole_0(k1_tarski(A_440),k2_tarski(A_440,B_441)) = k2_tarski(A_440,B_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5599,c_4,c_49440])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49488,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.85/15.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.85/15.92  
% 22.85/15.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.85/15.92  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 22.85/15.92  
% 22.85/15.92  %Foreground sorts:
% 22.85/15.92  
% 22.85/15.92  
% 22.85/15.92  %Background operators:
% 22.85/15.92  
% 22.85/15.92  
% 22.85/15.92  %Foreground operators:
% 22.85/15.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.85/15.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.85/15.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.85/15.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.85/15.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.85/15.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.85/15.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.85/15.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.85/15.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.85/15.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.85/15.92  tff('#skF_2', type, '#skF_2': $i).
% 22.85/15.92  tff('#skF_1', type, '#skF_1': $i).
% 22.85/15.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.85/15.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 22.85/15.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.85/15.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.85/15.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.85/15.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.85/15.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 22.85/15.92  
% 23.04/15.94  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 23.04/15.94  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 23.04/15.94  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 23.04/15.94  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.04/15.94  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.04/15.94  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 23.04/15.94  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 23.04/15.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.04/15.94  tff(f_63, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 23.04/15.94  tff(f_66, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 23.04/15.94  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.04/15.94  tff(c_97, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(A_55, B_56))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.04/15.94  tff(c_104, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 23.04/15.94  tff(c_177, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k4_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.04/15.94  tff(c_186, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_104, c_177])).
% 23.04/15.94  tff(c_192, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_186])).
% 23.04/15.94  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.04/15.94  tff(c_114, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.04/15.94  tff(c_122, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_114])).
% 23.04/15.94  tff(c_151, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.04/15.94  tff(c_160, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_122, c_151])).
% 23.04/15.94  tff(c_169, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_160])).
% 23.04/15.94  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.04/15.94  tff(c_272, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.04/15.94  tff(c_2128, plain, (![A_150, B_151, C_152]: (k5_xboole_0(A_150, k5_xboole_0(k4_xboole_0(B_151, A_150), C_152))=k5_xboole_0(k2_xboole_0(A_150, B_151), C_152))), inference(superposition, [status(thm), theory('equality')], [c_20, c_272])).
% 23.04/15.94  tff(c_2250, plain, (![A_150, B_151]: (k5_xboole_0(k2_xboole_0(A_150, B_151), k4_xboole_0(B_151, A_150))=k5_xboole_0(A_150, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2128])).
% 23.04/15.94  tff(c_2273, plain, (![A_153, B_154]: (k5_xboole_0(k2_xboole_0(A_153, B_154), k4_xboole_0(B_154, A_153))=A_153)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_2250])).
% 23.04/15.94  tff(c_929, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k5_xboole_0(B_121, k5_xboole_0(A_120, B_121)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_272])).
% 23.04/15.94  tff(c_501, plain, (![B_90, C_91]: (k5_xboole_0(B_90, k5_xboole_0(B_90, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_169, c_272])).
% 23.04/15.94  tff(c_561, plain, (![B_6]: (k5_xboole_0(k1_xboole_0, B_6)=k5_xboole_0(B_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_501])).
% 23.04/15.94  tff(c_579, plain, (![B_6]: (k5_xboole_0(k1_xboole_0, B_6)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_561])).
% 23.04/15.94  tff(c_328, plain, (![B_6, C_80]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_169, c_272])).
% 23.04/15.94  tff(c_580, plain, (![B_6, C_80]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_80))=C_80)), inference(demodulation, [status(thm), theory('equality')], [c_579, c_328])).
% 23.04/15.94  tff(c_937, plain, (![B_121, A_120]: (k5_xboole_0(B_121, k5_xboole_0(A_120, B_121))=k5_xboole_0(A_120, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_929, c_580])).
% 23.04/15.94  tff(c_1008, plain, (![B_121, A_120]: (k5_xboole_0(B_121, k5_xboole_0(A_120, B_121))=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_937])).
% 23.04/15.94  tff(c_2285, plain, (![B_154, A_153]: (k5_xboole_0(k4_xboole_0(B_154, A_153), A_153)=k2_xboole_0(A_153, B_154))), inference(superposition, [status(thm), theory('equality')], [c_2273, c_1008])).
% 23.04/15.94  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.04/15.94  tff(c_1584, plain, (![A_138, B_139, C_140]: (k5_xboole_0(A_138, k5_xboole_0(k3_xboole_0(A_138, B_139), C_140))=k5_xboole_0(k4_xboole_0(A_138, B_139), C_140))), inference(superposition, [status(thm), theory('equality')], [c_12, c_272])).
% 23.04/15.94  tff(c_1682, plain, (![A_138, B_139]: (k5_xboole_0(k4_xboole_0(A_138, B_139), k3_xboole_0(A_138, B_139))=k5_xboole_0(A_138, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_1584])).
% 23.04/15.94  tff(c_1708, plain, (![A_141, B_142]: (k5_xboole_0(k4_xboole_0(A_141, B_142), k3_xboole_0(A_141, B_142))=A_141)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_1682])).
% 23.04/15.94  tff(c_1726, plain, (![A_141, B_142]: (k5_xboole_0(k3_xboole_0(A_141, B_142), A_141)=k4_xboole_0(A_141, B_142))), inference(superposition, [status(thm), theory('equality')], [c_1708, c_1008])).
% 23.04/15.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.04/15.94  tff(c_163, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 23.04/15.94  tff(c_5367, plain, (![A_200, B_201, C_202]: (k5_xboole_0(A_200, k5_xboole_0(k3_xboole_0(B_201, A_200), C_202))=k5_xboole_0(k4_xboole_0(A_200, B_201), C_202))), inference(superposition, [status(thm), theory('equality')], [c_163, c_272])).
% 23.04/15.94  tff(c_5437, plain, (![B_142, A_141]: (k5_xboole_0(k4_xboole_0(B_142, A_141), A_141)=k5_xboole_0(B_142, k4_xboole_0(A_141, B_142)))), inference(superposition, [status(thm), theory('equality')], [c_1726, c_5367])).
% 23.04/15.94  tff(c_5599, plain, (![B_142, A_141]: (k2_xboole_0(B_142, A_141)=k2_xboole_0(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_2285, c_20, c_5437])).
% 23.04/15.94  tff(c_36, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.04/15.94  tff(c_252, plain, (![A_76, B_77]: (k3_xboole_0(k1_tarski(A_76), k2_tarski(A_76, B_77))=k1_tarski(A_76))), inference(resolution, [status(thm)], [c_36, c_114])).
% 23.04/15.94  tff(c_261, plain, (![A_76, B_77]: (k5_xboole_0(k1_tarski(A_76), k1_tarski(A_76))=k4_xboole_0(k1_tarski(A_76), k2_tarski(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_252, c_12])).
% 23.04/15.94  tff(c_346, plain, (![A_81, B_82]: (k4_xboole_0(k1_tarski(A_81), k2_tarski(A_81, B_82))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_261])).
% 23.04/15.94  tff(c_351, plain, (![A_81, B_82]: (k2_xboole_0(k2_tarski(A_81, B_82), k1_tarski(A_81))=k5_xboole_0(k2_tarski(A_81, B_82), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_346, c_20])).
% 23.04/15.94  tff(c_49317, plain, (![A_440, B_441]: (k2_xboole_0(k2_tarski(A_440, B_441), k1_tarski(A_440))=k2_tarski(A_440, B_441))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_351])).
% 23.04/15.94  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.04/15.94  tff(c_189, plain, (![A_11, B_12]: (k5_xboole_0(k2_xboole_0(A_11, B_12), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_177])).
% 23.04/15.94  tff(c_902, plain, (![A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_11, B_12), A_11)=k2_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_189])).
% 23.04/15.94  tff(c_49440, plain, (![A_440, B_441]: (k2_xboole_0(k2_tarski(A_440, B_441), k2_tarski(A_440, B_441))=k2_xboole_0(k2_tarski(A_440, B_441), k1_tarski(A_440)))), inference(superposition, [status(thm), theory('equality')], [c_49317, c_902])).
% 23.04/15.94  tff(c_49488, plain, (![A_440, B_441]: (k2_xboole_0(k1_tarski(A_440), k2_tarski(A_440, B_441))=k2_tarski(A_440, B_441))), inference(demodulation, [status(thm), theory('equality')], [c_5599, c_4, c_49440])).
% 23.04/15.94  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.04/15.94  tff(c_49496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49488, c_38])).
% 23.04/15.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.04/15.94  
% 23.04/15.94  Inference rules
% 23.04/15.94  ----------------------
% 23.04/15.94  #Ref     : 0
% 23.04/15.94  #Sup     : 12251
% 23.04/15.94  #Fact    : 0
% 23.04/15.94  #Define  : 0
% 23.04/15.94  #Split   : 0
% 23.04/15.94  #Chain   : 0
% 23.04/15.94  #Close   : 0
% 23.04/15.94  
% 23.04/15.94  Ordering : KBO
% 23.04/15.94  
% 23.04/15.94  Simplification rules
% 23.04/15.94  ----------------------
% 23.04/15.94  #Subsume      : 370
% 23.04/15.94  #Demod        : 23856
% 23.04/15.94  #Tautology    : 5266
% 23.04/15.94  #SimpNegUnit  : 0
% 23.04/15.94  #BackRed      : 5
% 23.04/15.94  
% 23.04/15.94  #Partial instantiations: 0
% 23.04/15.94  #Strategies tried      : 1
% 23.04/15.94  
% 23.04/15.94  Timing (in seconds)
% 23.04/15.94  ----------------------
% 23.04/15.94  Preprocessing        : 0.31
% 23.04/15.94  Parsing              : 0.16
% 23.04/15.94  CNF conversion       : 0.02
% 23.04/15.94  Main loop            : 14.88
% 23.04/15.94  Inferencing          : 1.63
% 23.04/15.94  Reduction            : 11.41
% 23.04/15.94  Demodulation         : 10.95
% 23.04/15.94  BG Simplification    : 0.30
% 23.04/15.94  Subsumption          : 1.27
% 23.04/15.94  Abstraction          : 0.53
% 23.04/15.94  MUC search           : 0.00
% 23.04/15.94  Cooper               : 0.00
% 23.04/15.94  Total                : 15.23
% 23.04/15.94  Index Insertion      : 0.00
% 23.04/15.94  Index Deletion       : 0.00
% 23.04/15.94  Index Matching       : 0.00
% 23.04/15.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
