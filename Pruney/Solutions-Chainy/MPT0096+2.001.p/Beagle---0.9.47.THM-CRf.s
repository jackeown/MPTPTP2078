%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 378 expanded)
%              Number of leaves         :   21 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :   74 ( 435 expanded)
%              Number of equality atoms :   60 ( 340 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_179,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_77,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_18])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_98,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [A_3] : k2_xboole_0(A_3,k4_xboole_0(A_3,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_120,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_116])).

tff(c_186,plain,(
    ! [B_35] : k3_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_120])).

tff(c_861,plain,(
    ! [B_63,A_64] : k2_xboole_0(k3_xboole_0(B_63,A_64),k4_xboole_0(A_64,B_63)) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_1010,plain,(
    ! [B_67] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_67,k1_xboole_0)) = B_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_861])).

tff(c_210,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_120])).

tff(c_286,plain,(
    ! [A_40] : k3_xboole_0(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_141,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_294,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_141])).

tff(c_1022,plain,(
    ! [B_67] : k4_xboole_0(B_67,k1_xboole_0) = B_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_294])).

tff(c_472,plain,(
    ! [A_47,B_48,C_49] : k3_xboole_0(k4_xboole_0(A_47,B_48),k4_xboole_0(A_47,C_49)) = k4_xboole_0(A_47,k2_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_509,plain,(
    ! [B_26,C_49] : k4_xboole_0(B_26,k2_xboole_0(B_26,C_49)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(B_26,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_472])).

tff(c_533,plain,(
    ! [B_50,C_51] : k4_xboole_0(B_50,k2_xboole_0(B_50,C_51)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_509])).

tff(c_568,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_533])).

tff(c_1063,plain,(
    ! [B_68] : k4_xboole_0(B_68,k1_xboole_0) = B_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_294])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k4_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1094,plain,(
    ! [B_68,C_12] : k4_xboole_0(B_68,k4_xboole_0(k1_xboole_0,C_12)) = k2_xboole_0(B_68,k3_xboole_0(B_68,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_12])).

tff(c_1554,plain,(
    ! [B_79,C_80] : k2_xboole_0(B_79,k3_xboole_0(B_79,C_80)) = B_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_568,c_1094])).

tff(c_1601,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1554])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_116])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = k2_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_20])).

tff(c_153,plain,(
    ! [A_32] : k2_xboole_0(A_32,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_148])).

tff(c_512,plain,(
    ! [B_26,B_48] : k4_xboole_0(B_26,k2_xboole_0(B_48,B_26)) = k3_xboole_0(k4_xboole_0(B_26,B_48),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_472])).

tff(c_531,plain,(
    ! [B_26,B_48] : k4_xboole_0(B_26,k2_xboole_0(B_48,B_26)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2,c_512])).

tff(c_886,plain,(
    ! [B_48,B_26] : k2_xboole_0(k3_xboole_0(k2_xboole_0(B_48,B_26),B_26),k1_xboole_0) = B_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_861])).

tff(c_925,plain,(
    ! [B_26,B_48] : k3_xboole_0(B_26,k2_xboole_0(B_48,B_26)) = B_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2,c_886])).

tff(c_336,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k4_xboole_0(A_41,B_42),k3_xboole_0(A_41,C_43)) = k4_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1451,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(k4_xboole_0(A_77,B_78),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_336])).

tff(c_704,plain,(
    ! [B_59,B_60] : k4_xboole_0(B_59,k2_xboole_0(B_60,B_59)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2,c_512])).

tff(c_777,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_704])).

tff(c_4577,plain,(
    ! [A_129,B_130] : k4_xboole_0(k2_xboole_0(k4_xboole_0(A_129,B_130),A_129),A_129) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_777])).

tff(c_248,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k4_xboole_0(A_37,B_38),C_39) = k4_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1711,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k2_xboole_0(B_84,k4_xboole_0(A_83,B_84))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_82])).

tff(c_110,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_1725,plain,(
    ! [B_84,A_83] : k2_xboole_0(k3_xboole_0(k2_xboole_0(B_84,k4_xboole_0(A_83,B_84)),A_83),k1_xboole_0) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_110])).

tff(c_1810,plain,(
    ! [A_83,B_84] : k3_xboole_0(A_83,k2_xboole_0(B_84,k4_xboole_0(A_83,B_84))) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2,c_1725])).

tff(c_4608,plain,(
    ! [A_129,B_130] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_129,B_130),A_129),k2_xboole_0(A_129,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_129,B_130),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_4577,c_1810])).

tff(c_4742,plain,(
    ! [A_129,B_130] : k2_xboole_0(k4_xboole_0(A_129,B_130),A_129) = A_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_2,c_120,c_4608])).

tff(c_366,plain,(
    ! [A_3,B_42] : k4_xboole_0(A_3,k4_xboole_0(B_42,A_3)) = k2_xboole_0(k4_xboole_0(A_3,B_42),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_336])).

tff(c_5128,plain,(
    ! [A_135,B_136] : k4_xboole_0(A_135,k4_xboole_0(B_136,A_135)) = A_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4742,c_366])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),k4_xboole_0(B_20,A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_267,plain,(
    ! [C_39,A_37,B_38] : r1_xboole_0(k4_xboole_0(C_39,k4_xboole_0(A_37,B_38)),k4_xboole_0(A_37,k2_xboole_0(B_38,C_39))) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_5167,plain,(
    ! [A_135,B_136] : r1_xboole_0(A_135,k4_xboole_0(B_136,k2_xboole_0(A_135,A_135))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5128,c_267])).

tff(c_5402,plain,(
    ! [A_139,B_140] : r1_xboole_0(A_139,k4_xboole_0(B_140,A_139)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_5167])).

tff(c_5682,plain,(
    ! [C_143,A_144,B_145] : r1_xboole_0(C_143,k4_xboole_0(A_144,k2_xboole_0(B_145,C_143))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5402])).

tff(c_5724,plain,(
    ! [B_2,A_1,A_144] : r1_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_144,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_5682])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5724,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  
% 4.40/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 4.40/1.79  
% 4.40/1.79  %Foreground sorts:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Background operators:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Foreground operators:
% 4.40/1.79  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.40/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.40/1.79  
% 4.40/1.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.40/1.81  tff(f_34, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.40/1.81  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 4.40/1.81  tff(f_54, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 4.40/1.81  tff(f_50, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.40/1.81  tff(f_30, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.40/1.81  tff(f_38, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 4.40/1.81  tff(f_36, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.40/1.81  tff(f_32, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.40/1.81  tff(f_57, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 4.40/1.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.81  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.40/1.81  tff(c_121, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.40/1.81  tff(c_136, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=k2_xboole_0(k3_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_121])).
% 4.40/1.81  tff(c_179, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 4.40/1.81  tff(c_77, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.40/1.81  tff(c_18, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/1.81  tff(c_82, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_18])).
% 4.40/1.81  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.40/1.81  tff(c_98, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.40/1.81  tff(c_116, plain, (![A_3]: (k2_xboole_0(A_3, k4_xboole_0(A_3, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_6, c_98])).
% 4.40/1.81  tff(c_120, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_116])).
% 4.40/1.81  tff(c_186, plain, (![B_35]: (k3_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_120])).
% 4.40/1.81  tff(c_861, plain, (![B_63, A_64]: (k2_xboole_0(k3_xboole_0(B_63, A_64), k4_xboole_0(A_64, B_63))=A_64)), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 4.40/1.81  tff(c_1010, plain, (![B_67]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_67, k1_xboole_0))=B_67)), inference(superposition, [status(thm), theory('equality')], [c_186, c_861])).
% 4.40/1.81  tff(c_210, plain, (![B_36]: (k3_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_120])).
% 4.40/1.81  tff(c_286, plain, (![A_40]: (k3_xboole_0(A_40, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_210])).
% 4.40/1.81  tff(c_141, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 4.40/1.81  tff(c_294, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_286, c_141])).
% 4.40/1.81  tff(c_1022, plain, (![B_67]: (k4_xboole_0(B_67, k1_xboole_0)=B_67)), inference(superposition, [status(thm), theory('equality')], [c_1010, c_294])).
% 4.40/1.81  tff(c_472, plain, (![A_47, B_48, C_49]: (k3_xboole_0(k4_xboole_0(A_47, B_48), k4_xboole_0(A_47, C_49))=k4_xboole_0(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.40/1.81  tff(c_509, plain, (![B_26, C_49]: (k4_xboole_0(B_26, k2_xboole_0(B_26, C_49))=k3_xboole_0(k1_xboole_0, k4_xboole_0(B_26, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_472])).
% 4.40/1.81  tff(c_533, plain, (![B_50, C_51]: (k4_xboole_0(B_50, k2_xboole_0(B_50, C_51))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_509])).
% 4.40/1.81  tff(c_568, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_533])).
% 4.40/1.81  tff(c_1063, plain, (![B_68]: (k4_xboole_0(B_68, k1_xboole_0)=B_68)), inference(superposition, [status(thm), theory('equality')], [c_1010, c_294])).
% 4.40/1.81  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k4_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.40/1.81  tff(c_1094, plain, (![B_68, C_12]: (k4_xboole_0(B_68, k4_xboole_0(k1_xboole_0, C_12))=k2_xboole_0(B_68, k3_xboole_0(B_68, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_12])).
% 4.40/1.81  tff(c_1554, plain, (![B_79, C_80]: (k2_xboole_0(B_79, k3_xboole_0(B_79, C_80))=B_79)), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_568, c_1094])).
% 4.40/1.81  tff(c_1601, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1554])).
% 4.40/1.81  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.40/1.81  tff(c_142, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_116])).
% 4.40/1.81  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.40/1.81  tff(c_148, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=k2_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_142, c_20])).
% 4.40/1.81  tff(c_153, plain, (![A_32]: (k2_xboole_0(A_32, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_148])).
% 4.40/1.81  tff(c_512, plain, (![B_26, B_48]: (k4_xboole_0(B_26, k2_xboole_0(B_48, B_26))=k3_xboole_0(k4_xboole_0(B_26, B_48), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_472])).
% 4.40/1.81  tff(c_531, plain, (![B_26, B_48]: (k4_xboole_0(B_26, k2_xboole_0(B_48, B_26))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_2, c_512])).
% 4.40/1.81  tff(c_886, plain, (![B_48, B_26]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(B_48, B_26), B_26), k1_xboole_0)=B_26)), inference(superposition, [status(thm), theory('equality')], [c_531, c_861])).
% 4.40/1.81  tff(c_925, plain, (![B_26, B_48]: (k3_xboole_0(B_26, k2_xboole_0(B_48, B_26))=B_26)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2, c_886])).
% 4.40/1.81  tff(c_336, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k4_xboole_0(A_41, B_42), k3_xboole_0(A_41, C_43))=k4_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.40/1.81  tff(c_1451, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(k4_xboole_0(A_77, B_78), A_77))), inference(superposition, [status(thm), theory('equality')], [c_6, c_336])).
% 4.40/1.81  tff(c_704, plain, (![B_59, B_60]: (k4_xboole_0(B_59, k2_xboole_0(B_60, B_59))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_2, c_512])).
% 4.40/1.81  tff(c_777, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_704])).
% 4.40/1.81  tff(c_4577, plain, (![A_129, B_130]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_129, B_130), A_129), A_129)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1451, c_777])).
% 4.40/1.81  tff(c_248, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k4_xboole_0(A_37, B_38), C_39)=k4_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.40/1.81  tff(c_1711, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k2_xboole_0(B_84, k4_xboole_0(A_83, B_84)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_248, c_82])).
% 4.40/1.81  tff(c_110, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 4.40/1.81  tff(c_1725, plain, (![B_84, A_83]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(B_84, k4_xboole_0(A_83, B_84)), A_83), k1_xboole_0)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_1711, c_110])).
% 4.40/1.81  tff(c_1810, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k2_xboole_0(B_84, k4_xboole_0(A_83, B_84)))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2, c_1725])).
% 4.40/1.81  tff(c_4608, plain, (![A_129, B_130]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_129, B_130), A_129), k2_xboole_0(A_129, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_129, B_130), A_129))), inference(superposition, [status(thm), theory('equality')], [c_4577, c_1810])).
% 4.40/1.81  tff(c_4742, plain, (![A_129, B_130]: (k2_xboole_0(k4_xboole_0(A_129, B_130), A_129)=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_925, c_2, c_120, c_4608])).
% 4.40/1.81  tff(c_366, plain, (![A_3, B_42]: (k4_xboole_0(A_3, k4_xboole_0(B_42, A_3))=k2_xboole_0(k4_xboole_0(A_3, B_42), A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_336])).
% 4.40/1.81  tff(c_5128, plain, (![A_135, B_136]: (k4_xboole_0(A_135, k4_xboole_0(B_136, A_135))=A_135)), inference(demodulation, [status(thm), theory('equality')], [c_4742, c_366])).
% 4.40/1.81  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.40/1.81  tff(c_267, plain, (![C_39, A_37, B_38]: (r1_xboole_0(k4_xboole_0(C_39, k4_xboole_0(A_37, B_38)), k4_xboole_0(A_37, k2_xboole_0(B_38, C_39))))), inference(superposition, [status(thm), theory('equality')], [c_248, c_22])).
% 4.40/1.81  tff(c_5167, plain, (![A_135, B_136]: (r1_xboole_0(A_135, k4_xboole_0(B_136, k2_xboole_0(A_135, A_135))))), inference(superposition, [status(thm), theory('equality')], [c_5128, c_267])).
% 4.40/1.81  tff(c_5402, plain, (![A_139, B_140]: (r1_xboole_0(A_139, k4_xboole_0(B_140, A_139)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_5167])).
% 4.40/1.81  tff(c_5682, plain, (![C_143, A_144, B_145]: (r1_xboole_0(C_143, k4_xboole_0(A_144, k2_xboole_0(B_145, C_143))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5402])).
% 4.40/1.81  tff(c_5724, plain, (![B_2, A_1, A_144]: (r1_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_144, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_5682])).
% 4.40/1.81  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.40/1.81  tff(c_5930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5724, c_24])).
% 4.40/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.81  
% 4.40/1.81  Inference rules
% 4.40/1.81  ----------------------
% 4.40/1.81  #Ref     : 0
% 4.40/1.81  #Sup     : 1489
% 4.40/1.81  #Fact    : 0
% 4.40/1.81  #Define  : 0
% 4.40/1.81  #Split   : 0
% 4.40/1.81  #Chain   : 0
% 4.40/1.81  #Close   : 0
% 4.40/1.81  
% 4.40/1.81  Ordering : KBO
% 4.40/1.81  
% 4.40/1.81  Simplification rules
% 4.40/1.81  ----------------------
% 4.40/1.81  #Subsume      : 0
% 4.40/1.81  #Demod        : 1324
% 4.40/1.81  #Tautology    : 1031
% 4.40/1.81  #SimpNegUnit  : 0
% 4.40/1.81  #BackRed      : 4
% 4.40/1.81  
% 4.40/1.81  #Partial instantiations: 0
% 4.40/1.81  #Strategies tried      : 1
% 4.40/1.81  
% 4.40/1.81  Timing (in seconds)
% 4.40/1.81  ----------------------
% 4.40/1.81  Preprocessing        : 0.28
% 4.40/1.81  Parsing              : 0.15
% 4.40/1.81  CNF conversion       : 0.01
% 4.40/1.81  Main loop            : 0.75
% 4.40/1.81  Inferencing          : 0.24
% 4.40/1.81  Reduction            : 0.34
% 4.40/1.81  Demodulation         : 0.28
% 4.40/1.81  BG Simplification    : 0.03
% 4.40/1.81  Subsumption          : 0.10
% 4.40/1.81  Abstraction          : 0.04
% 4.52/1.81  MUC search           : 0.00
% 4.52/1.81  Cooper               : 0.00
% 4.52/1.81  Total                : 1.07
% 4.52/1.81  Index Insertion      : 0.00
% 4.52/1.81  Index Deletion       : 0.00
% 4.52/1.81  Index Matching       : 0.00
% 4.52/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
