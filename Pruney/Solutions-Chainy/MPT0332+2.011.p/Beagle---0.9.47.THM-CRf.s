%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   81 (1101 expanded)
%              Number of leaves         :   26 ( 392 expanded)
%              Depth                    :   20
%              Number of atoms          :   72 (1096 expanded)
%              Number of equality atoms :   61 (1081 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [C_27,A_25,B_26] :
      ( k4_xboole_0(C_27,k2_tarski(A_25,B_26)) = C_27
      | r2_hidden(B_26,C_27)
      | r2_hidden(A_25,C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [A_50,B_51,C_52] : k5_xboole_0(k5_xboole_0(A_50,B_51),C_52) = k5_xboole_0(A_50,k5_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_321,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k5_xboole_0(B_54,k5_xboole_0(A_53,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_12])).

tff(c_361,plain,(
    ! [A_11] : k5_xboole_0(A_11,k5_xboole_0(A_11,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_321])).

tff(c_370,plain,(
    ! [A_11] : k5_xboole_0(A_11,k4_xboole_0(A_11,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_361])).

tff(c_568,plain,(
    ! [A_64,C_65] : k5_xboole_0(A_64,k5_xboole_0(A_64,C_65)) = k5_xboole_0(k1_xboole_0,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_256])).

tff(c_610,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k4_xboole_0(A_11,k1_xboole_0)) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_568])).

tff(c_647,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_16,c_610])).

tff(c_639,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_568])).

tff(c_653,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_639])).

tff(c_855,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_653])).

tff(c_54,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_33,B_32] : k3_xboole_0(A_33,k2_xboole_0(B_32,A_33)) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_352,plain,(
    ! [A_7] : k5_xboole_0(A_7,k5_xboole_0(k1_xboole_0,k4_xboole_0(A_7,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_321])).

tff(c_369,plain,(
    ! [A_7] : k5_xboole_0(A_7,k2_xboole_0(k1_xboole_0,A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_352])).

tff(c_441,plain,(
    ! [A_57,B_58] : k5_xboole_0(k5_xboole_0(A_57,B_58),k2_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1679,plain,(
    ! [B_86,A_87] : k5_xboole_0(k5_xboole_0(B_86,A_87),k2_xboole_0(A_87,B_86)) = k3_xboole_0(B_86,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_1750,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,A_7),A_7)) = k3_xboole_0(A_7,k2_xboole_0(k1_xboole_0,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_1679])).

tff(c_1793,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_7,k2_xboole_0(k1_xboole_0,A_7))) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_69,c_2,c_1750])).

tff(c_1867,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_89,k2_xboole_0(k1_xboole_0,A_89))) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_69,c_2,c_1750])).

tff(c_754,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,A_67) = k4_xboole_0(A_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_639])).

tff(c_833,plain,(
    ! [B_15] : k4_xboole_0(k4_xboole_0(B_15,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_754])).

tff(c_1608,plain,(
    ! [B_15] : k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,B_15)) = k2_xboole_0(k1_xboole_0,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_647,c_833])).

tff(c_1882,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_89,k2_xboole_0(k1_xboole_0,A_89))) = k2_xboole_0(k1_xboole_0,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_1867,c_1608])).

tff(c_1946,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,A_89) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_1882])).

tff(c_308,plain,(
    ! [A_11,C_52] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_52)) = k5_xboole_0(k1_xboole_0,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_256])).

tff(c_752,plain,(
    ! [A_11,C_52] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_52)) = k4_xboole_0(C_52,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_308])).

tff(c_1276,plain,(
    ! [A_11,C_52] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_52)) = k2_xboole_0(k1_xboole_0,C_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_752])).

tff(c_2546,plain,(
    ! [A_101,C_102] : k5_xboole_0(A_101,k5_xboole_0(A_101,C_102)) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1946,c_1276])).

tff(c_2640,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k4_xboole_0(B_15,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2546])).

tff(c_857,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_154])).

tff(c_1965,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1946,c_857])).

tff(c_151,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_139])).

tff(c_158,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_151])).

tff(c_2779,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(A_105,k5_xboole_0(k4_xboole_0(B_106,A_105),C_107)) = k5_xboole_0(k2_xboole_0(A_105,B_106),C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_2894,plain,(
    ! [A_105,B_106] : k5_xboole_0(k2_xboole_0(A_105,B_106),k4_xboole_0(B_106,A_105)) = k5_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2779])).

tff(c_3715,plain,(
    ! [A_121,B_122] : k5_xboole_0(k2_xboole_0(A_121,B_122),k4_xboole_0(B_122,A_121)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_2894])).

tff(c_3772,plain,(
    ! [A_5,B_6] : k5_xboole_0(k2_xboole_0(k2_xboole_0(A_5,B_6),A_5),k1_xboole_0) = k2_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_3715])).

tff(c_4872,plain,(
    ! [A_141,B_142] : k2_xboole_0(A_141,k2_xboole_0(A_141,B_142)) = k2_xboole_0(A_141,B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_2,c_3772])).

tff(c_5555,plain,(
    ! [B_155,A_156] : k2_xboole_0(B_155,k2_xboole_0(A_156,B_155)) = k2_xboole_0(B_155,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4872])).

tff(c_5596,plain,(
    ! [B_155,A_156] : k5_xboole_0(B_155,k2_xboole_0(B_155,A_156)) = k4_xboole_0(k2_xboole_0(A_156,B_155),B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_5555,c_2640])).

tff(c_5686,plain,(
    ! [A_156,B_155] : k4_xboole_0(k2_xboole_0(A_156,B_155),B_155) = k4_xboole_0(A_156,B_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_5596])).

tff(c_26,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8751,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5686,c_26])).

tff(c_8912,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8751])).

tff(c_8916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_8912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.64  
% 6.47/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.65  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.47/2.65  
% 6.47/2.65  %Foreground sorts:
% 6.47/2.65  
% 6.47/2.65  
% 6.47/2.65  %Background operators:
% 6.47/2.65  
% 6.47/2.65  
% 6.47/2.65  %Foreground operators:
% 6.47/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.47/2.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.47/2.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.65  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.65  tff('#skF_3', type, '#skF_3': $i).
% 6.47/2.65  tff('#skF_1', type, '#skF_1': $i).
% 6.47/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.47/2.65  
% 6.47/2.66  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 6.47/2.66  tff(f_57, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 6.47/2.66  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.47/2.66  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.47/2.66  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.47/2.66  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.47/2.66  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.47/2.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.47/2.66  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.47/2.66  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.47/2.66  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.66  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.66  tff(c_24, plain, (![C_27, A_25, B_26]: (k4_xboole_0(C_27, k2_tarski(A_25, B_26))=C_27 | r2_hidden(B_26, C_27) | r2_hidden(A_25, C_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.47/2.66  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.66  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.47/2.66  tff(c_139, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.66  tff(c_154, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_139])).
% 6.47/2.66  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.47/2.66  tff(c_256, plain, (![A_50, B_51, C_52]: (k5_xboole_0(k5_xboole_0(A_50, B_51), C_52)=k5_xboole_0(A_50, k5_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.47/2.66  tff(c_321, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k5_xboole_0(B_54, k5_xboole_0(A_53, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_12])).
% 6.47/2.66  tff(c_361, plain, (![A_11]: (k5_xboole_0(A_11, k5_xboole_0(A_11, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_321])).
% 6.47/2.66  tff(c_370, plain, (![A_11]: (k5_xboole_0(A_11, k4_xboole_0(A_11, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_361])).
% 6.47/2.66  tff(c_568, plain, (![A_64, C_65]: (k5_xboole_0(A_64, k5_xboole_0(A_64, C_65))=k5_xboole_0(k1_xboole_0, C_65))), inference(superposition, [status(thm), theory('equality')], [c_12, c_256])).
% 6.47/2.66  tff(c_610, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(A_11, k1_xboole_0))=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_370, c_568])).
% 6.47/2.66  tff(c_647, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_16, c_610])).
% 6.47/2.66  tff(c_639, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_568])).
% 6.47/2.66  tff(c_653, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k4_xboole_0(A_11, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_639])).
% 6.47/2.66  tff(c_855, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_653])).
% 6.47/2.66  tff(c_54, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.66  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.47/2.66  tff(c_69, plain, (![A_33, B_32]: (k3_xboole_0(A_33, k2_xboole_0(B_32, A_33))=A_33)), inference(superposition, [status(thm), theory('equality')], [c_54, c_6])).
% 6.47/2.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.66  tff(c_352, plain, (![A_7]: (k5_xboole_0(A_7, k5_xboole_0(k1_xboole_0, k4_xboole_0(A_7, k1_xboole_0)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_321])).
% 6.47/2.66  tff(c_369, plain, (![A_7]: (k5_xboole_0(A_7, k2_xboole_0(k1_xboole_0, A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_352])).
% 6.47/2.66  tff(c_441, plain, (![A_57, B_58]: (k5_xboole_0(k5_xboole_0(A_57, B_58), k2_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.47/2.66  tff(c_1679, plain, (![B_86, A_87]: (k5_xboole_0(k5_xboole_0(B_86, A_87), k2_xboole_0(A_87, B_86))=k3_xboole_0(B_86, A_87))), inference(superposition, [status(thm), theory('equality')], [c_2, c_441])).
% 6.47/2.66  tff(c_1750, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(k2_xboole_0(k1_xboole_0, A_7), A_7))=k3_xboole_0(A_7, k2_xboole_0(k1_xboole_0, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_369, c_1679])).
% 6.47/2.66  tff(c_1793, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_7, k2_xboole_0(k1_xboole_0, A_7)))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_855, c_69, c_2, c_1750])).
% 6.47/2.66  tff(c_1867, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_89, k2_xboole_0(k1_xboole_0, A_89)))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_855, c_69, c_2, c_1750])).
% 6.47/2.66  tff(c_754, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, A_67)=k4_xboole_0(A_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_639])).
% 6.47/2.66  tff(c_833, plain, (![B_15]: (k4_xboole_0(k4_xboole_0(B_15, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_754])).
% 6.47/2.66  tff(c_1608, plain, (![B_15]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, B_15))=k2_xboole_0(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_647, c_833])).
% 6.47/2.66  tff(c_1882, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_89, k2_xboole_0(k1_xboole_0, A_89)))=k2_xboole_0(k1_xboole_0, A_89))), inference(superposition, [status(thm), theory('equality')], [c_1867, c_1608])).
% 6.47/2.66  tff(c_1946, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, A_89)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_1793, c_1882])).
% 6.47/2.66  tff(c_308, plain, (![A_11, C_52]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_52))=k5_xboole_0(k1_xboole_0, C_52))), inference(superposition, [status(thm), theory('equality')], [c_12, c_256])).
% 6.47/2.66  tff(c_752, plain, (![A_11, C_52]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_52))=k4_xboole_0(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_308])).
% 6.47/2.66  tff(c_1276, plain, (![A_11, C_52]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_52))=k2_xboole_0(k1_xboole_0, C_52))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_752])).
% 6.47/2.66  tff(c_2546, plain, (![A_101, C_102]: (k5_xboole_0(A_101, k5_xboole_0(A_101, C_102))=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_1946, c_1276])).
% 6.47/2.66  tff(c_2640, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k4_xboole_0(B_15, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2546])).
% 6.47/2.66  tff(c_857, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_154])).
% 6.47/2.66  tff(c_1965, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_1946, c_857])).
% 6.47/2.66  tff(c_151, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_139])).
% 6.47/2.66  tff(c_158, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_151])).
% 6.47/2.66  tff(c_2779, plain, (![A_105, B_106, C_107]: (k5_xboole_0(A_105, k5_xboole_0(k4_xboole_0(B_106, A_105), C_107))=k5_xboole_0(k2_xboole_0(A_105, B_106), C_107))), inference(superposition, [status(thm), theory('equality')], [c_16, c_256])).
% 6.47/2.66  tff(c_2894, plain, (![A_105, B_106]: (k5_xboole_0(k2_xboole_0(A_105, B_106), k4_xboole_0(B_106, A_105))=k5_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2779])).
% 6.47/2.66  tff(c_3715, plain, (![A_121, B_122]: (k5_xboole_0(k2_xboole_0(A_121, B_122), k4_xboole_0(B_122, A_121))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_2894])).
% 6.47/2.66  tff(c_3772, plain, (![A_5, B_6]: (k5_xboole_0(k2_xboole_0(k2_xboole_0(A_5, B_6), A_5), k1_xboole_0)=k2_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_158, c_3715])).
% 6.47/2.66  tff(c_4872, plain, (![A_141, B_142]: (k2_xboole_0(A_141, k2_xboole_0(A_141, B_142))=k2_xboole_0(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_2, c_3772])).
% 6.47/2.66  tff(c_5555, plain, (![B_155, A_156]: (k2_xboole_0(B_155, k2_xboole_0(A_156, B_155))=k2_xboole_0(B_155, A_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4872])).
% 6.47/2.66  tff(c_5596, plain, (![B_155, A_156]: (k5_xboole_0(B_155, k2_xboole_0(B_155, A_156))=k4_xboole_0(k2_xboole_0(A_156, B_155), B_155))), inference(superposition, [status(thm), theory('equality')], [c_5555, c_2640])).
% 6.47/2.66  tff(c_5686, plain, (![A_156, B_155]: (k4_xboole_0(k2_xboole_0(A_156, B_155), B_155)=k4_xboole_0(A_156, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_5596])).
% 6.47/2.66  tff(c_26, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.66  tff(c_8751, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5686, c_26])).
% 6.47/2.66  tff(c_8912, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_8751])).
% 6.47/2.66  tff(c_8916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_8912])).
% 6.47/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.66  
% 6.47/2.66  Inference rules
% 6.47/2.66  ----------------------
% 6.47/2.66  #Ref     : 0
% 6.47/2.66  #Sup     : 2181
% 6.47/2.66  #Fact    : 0
% 6.47/2.66  #Define  : 0
% 6.47/2.66  #Split   : 1
% 6.47/2.66  #Chain   : 0
% 6.47/2.66  #Close   : 0
% 6.47/2.66  
% 6.47/2.66  Ordering : KBO
% 6.47/2.66  
% 6.47/2.66  Simplification rules
% 6.47/2.66  ----------------------
% 6.47/2.66  #Subsume      : 35
% 6.47/2.66  #Demod        : 2981
% 6.47/2.66  #Tautology    : 1226
% 6.47/2.66  #SimpNegUnit  : 1
% 6.47/2.66  #BackRed      : 21
% 6.47/2.66  
% 6.47/2.66  #Partial instantiations: 0
% 6.47/2.66  #Strategies tried      : 1
% 6.47/2.66  
% 6.47/2.66  Timing (in seconds)
% 6.47/2.66  ----------------------
% 6.47/2.67  Preprocessing        : 0.29
% 6.47/2.67  Parsing              : 0.16
% 6.47/2.67  CNF conversion       : 0.02
% 6.47/2.67  Main loop            : 1.60
% 6.47/2.67  Inferencing          : 0.39
% 6.47/2.67  Reduction            : 0.90
% 6.47/2.67  Demodulation         : 0.80
% 6.47/2.67  BG Simplification    : 0.06
% 6.47/2.67  Subsumption          : 0.18
% 6.47/2.67  Abstraction          : 0.09
% 6.47/2.67  MUC search           : 0.00
% 6.47/2.67  Cooper               : 0.00
% 6.47/2.67  Total                : 1.92
% 6.47/2.67  Index Insertion      : 0.00
% 6.47/2.67  Index Deletion       : 0.00
% 6.47/2.67  Index Matching       : 0.00
% 6.47/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
