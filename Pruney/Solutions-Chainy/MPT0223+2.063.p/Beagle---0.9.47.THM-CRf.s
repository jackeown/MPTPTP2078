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
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 172 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 169 expanded)
%              Number of equality atoms :   66 ( 161 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_143,plain,(
    ! [C_76,B_77,A_78] : k1_enumset1(C_76,B_77,A_78) = k1_enumset1(A_78,B_77,C_76) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_159,plain,(
    ! [C_76,B_77] : k1_enumset1(C_76,B_77,B_77) = k2_tarski(B_77,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_42])).

tff(c_40,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_543,plain,(
    ! [A_99,B_100,C_101,D_102] : k2_xboole_0(k2_tarski(A_99,B_100),k2_tarski(C_101,D_102)) = k2_enumset1(A_99,B_100,C_101,D_102) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_579,plain,(
    ! [A_24,C_101,D_102] : k2_xboole_0(k1_tarski(A_24),k2_tarski(C_101,D_102)) = k2_enumset1(A_24,A_24,C_101,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_543])).

tff(c_1036,plain,(
    ! [A_155,C_156,D_157] : k2_xboole_0(k1_tarski(A_155),k2_tarski(C_156,D_157)) = k1_enumset1(A_155,C_156,D_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_579])).

tff(c_1072,plain,(
    ! [A_155,A_24] : k2_xboole_0(k1_tarski(A_155),k1_tarski(A_24)) = k1_enumset1(A_155,A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1036])).

tff(c_1084,plain,(
    ! [A_158,A_159] : k2_xboole_0(k1_tarski(A_158),k1_tarski(A_159)) = k2_tarski(A_159,A_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1072])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_142,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_139])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_136,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_127])).

tff(c_281,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_136])).

tff(c_288,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_297,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_288])).

tff(c_303,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_297])).

tff(c_1115,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_303])).

tff(c_94,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [A_67,B_68] : r2_hidden(A_67,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_18])).

tff(c_1176,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_106])).

tff(c_593,plain,(
    ! [A_103,B_104,C_105,D_106] : k4_xboole_0(k2_tarski(A_103,B_104),k2_enumset1(A_103,B_104,C_105,D_106)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_6])).

tff(c_603,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k2_tarski(A_27,A_27),k1_enumset1(A_27,B_28,C_29)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_593])).

tff(c_612,plain,(
    ! [A_107,B_108,C_109] : k4_xboole_0(k1_tarski(A_107),k1_enumset1(A_107,B_108,C_109)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_603])).

tff(c_689,plain,(
    ! [A_117,B_118] : k4_xboole_0(k1_tarski(A_117),k2_tarski(A_117,B_118)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_612])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_697,plain,(
    ! [A_117,B_118] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(A_117)) = k5_xboole_0(k2_tarski(A_117,B_118),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_10])).

tff(c_708,plain,(
    ! [A_117,B_118] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(A_117)) = k2_tarski(A_117,B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_697])).

tff(c_36,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k2_tarski(A_17,B_18),k2_tarski(C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_827,plain,(
    ! [A_135,B_136] : k2_xboole_0(k2_tarski(A_135,B_136),k1_tarski(A_135)) = k2_tarski(A_135,B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_697])).

tff(c_300,plain,(
    ! [A_5,B_6] : k5_xboole_0(k2_xboole_0(A_5,B_6),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_288])).

tff(c_304,plain,(
    ! [A_5,B_6] : k2_xboole_0(k2_xboole_0(A_5,B_6),A_5) = k2_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_300])).

tff(c_352,plain,(
    ! [A_87,B_88] : k2_xboole_0(k2_xboole_0(A_87,B_88),A_87) = k2_xboole_0(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_300])).

tff(c_355,plain,(
    ! [A_87,B_88] : k2_xboole_0(k2_xboole_0(A_87,B_88),k2_xboole_0(A_87,B_88)) = k2_xboole_0(k2_xboole_0(A_87,B_88),A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_304])).

tff(c_377,plain,(
    ! [A_87,B_88] : k2_xboole_0(k2_xboole_0(A_87,B_88),k2_xboole_0(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_355])).

tff(c_833,plain,(
    ! [A_135,B_136] : k2_xboole_0(k2_tarski(A_135,B_136),k2_xboole_0(k2_tarski(A_135,B_136),k1_tarski(A_135))) = k2_xboole_0(k2_tarski(A_135,B_136),k1_tarski(A_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_377])).

tff(c_874,plain,(
    ! [A_137,B_138] : k2_enumset1(A_137,B_138,A_137,B_138) = k2_tarski(A_137,B_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_36,c_708,c_833])).

tff(c_884,plain,(
    ! [B_138] : k1_enumset1(B_138,B_138,B_138) = k2_tarski(B_138,B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_44])).

tff(c_896,plain,(
    ! [B_139] : k1_enumset1(B_139,B_139,B_139) = k1_tarski(B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_884])).

tff(c_12,plain,(
    ! [E_16,C_12,B_11,A_10] :
      ( E_16 = C_12
      | E_16 = B_11
      | E_16 = A_10
      | ~ r2_hidden(E_16,k1_enumset1(A_10,B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2555,plain,(
    ! [E_228,B_229] :
      ( E_228 = B_229
      | E_228 = B_229
      | E_228 = B_229
      | ~ r2_hidden(E_228,k1_tarski(B_229)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_12])).

tff(c_2562,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1176,c_2555])).

tff(c_2570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_2562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n003.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 13:12:27 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  
% 3.38/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.38/1.56  
% 3.38/1.56  %Foreground sorts:
% 3.38/1.56  
% 3.38/1.56  
% 3.38/1.56  %Background operators:
% 3.38/1.56  
% 3.38/1.56  
% 3.38/1.56  %Foreground operators:
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.38/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.38/1.56  
% 3.38/1.58  tff(f_73, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.38/1.58  tff(f_54, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 3.38/1.58  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.38/1.58  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.38/1.58  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.38/1.58  tff(f_52, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.38/1.58  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.58  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.38/1.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.38/1.58  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.58  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.38/1.58  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.38/1.58  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.58  tff(c_143, plain, (![C_76, B_77, A_78]: (k1_enumset1(C_76, B_77, A_78)=k1_enumset1(A_78, B_77, C_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.38/1.58  tff(c_42, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.58  tff(c_159, plain, (![C_76, B_77]: (k1_enumset1(C_76, B_77, B_77)=k2_tarski(B_77, C_76))), inference(superposition, [status(thm), theory('equality')], [c_143, c_42])).
% 3.38/1.58  tff(c_40, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.58  tff(c_44, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.58  tff(c_543, plain, (![A_99, B_100, C_101, D_102]: (k2_xboole_0(k2_tarski(A_99, B_100), k2_tarski(C_101, D_102))=k2_enumset1(A_99, B_100, C_101, D_102))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.38/1.58  tff(c_579, plain, (![A_24, C_101, D_102]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(C_101, D_102))=k2_enumset1(A_24, A_24, C_101, D_102))), inference(superposition, [status(thm), theory('equality')], [c_40, c_543])).
% 3.38/1.58  tff(c_1036, plain, (![A_155, C_156, D_157]: (k2_xboole_0(k1_tarski(A_155), k2_tarski(C_156, D_157))=k1_enumset1(A_155, C_156, D_157))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_579])).
% 3.38/1.58  tff(c_1072, plain, (![A_155, A_24]: (k2_xboole_0(k1_tarski(A_155), k1_tarski(A_24))=k1_enumset1(A_155, A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1036])).
% 3.38/1.58  tff(c_1084, plain, (![A_158, A_159]: (k2_xboole_0(k1_tarski(A_158), k1_tarski(A_159))=k2_tarski(A_159, A_158))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_1072])).
% 3.38/1.58  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.58  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.58  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.58  tff(c_127, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.58  tff(c_139, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_127])).
% 3.38/1.58  tff(c_142, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_139])).
% 3.38/1.58  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.58  tff(c_136, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_127])).
% 3.38/1.58  tff(c_281, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_142, c_136])).
% 3.38/1.58  tff(c_288, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.58  tff(c_297, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_281, c_288])).
% 3.38/1.58  tff(c_303, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_297])).
% 3.38/1.58  tff(c_1115, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1084, c_303])).
% 3.38/1.58  tff(c_94, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.58  tff(c_18, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.58  tff(c_106, plain, (![A_67, B_68]: (r2_hidden(A_67, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_18])).
% 3.38/1.58  tff(c_1176, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1115, c_106])).
% 3.38/1.58  tff(c_593, plain, (![A_103, B_104, C_105, D_106]: (k4_xboole_0(k2_tarski(A_103, B_104), k2_enumset1(A_103, B_104, C_105, D_106))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_543, c_6])).
% 3.38/1.58  tff(c_603, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k2_tarski(A_27, A_27), k1_enumset1(A_27, B_28, C_29))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_593])).
% 3.38/1.58  tff(c_612, plain, (![A_107, B_108, C_109]: (k4_xboole_0(k1_tarski(A_107), k1_enumset1(A_107, B_108, C_109))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_603])).
% 3.38/1.58  tff(c_689, plain, (![A_117, B_118]: (k4_xboole_0(k1_tarski(A_117), k2_tarski(A_117, B_118))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_612])).
% 3.38/1.58  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.58  tff(c_697, plain, (![A_117, B_118]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(A_117))=k5_xboole_0(k2_tarski(A_117, B_118), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_689, c_10])).
% 3.38/1.58  tff(c_708, plain, (![A_117, B_118]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(A_117))=k2_tarski(A_117, B_118))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_697])).
% 3.38/1.58  tff(c_36, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k2_tarski(A_17, B_18), k2_tarski(C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.38/1.58  tff(c_827, plain, (![A_135, B_136]: (k2_xboole_0(k2_tarski(A_135, B_136), k1_tarski(A_135))=k2_tarski(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_697])).
% 3.38/1.58  tff(c_300, plain, (![A_5, B_6]: (k5_xboole_0(k2_xboole_0(A_5, B_6), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_288])).
% 3.38/1.58  tff(c_304, plain, (![A_5, B_6]: (k2_xboole_0(k2_xboole_0(A_5, B_6), A_5)=k2_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_300])).
% 3.38/1.58  tff(c_352, plain, (![A_87, B_88]: (k2_xboole_0(k2_xboole_0(A_87, B_88), A_87)=k2_xboole_0(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_300])).
% 3.38/1.58  tff(c_355, plain, (![A_87, B_88]: (k2_xboole_0(k2_xboole_0(A_87, B_88), k2_xboole_0(A_87, B_88))=k2_xboole_0(k2_xboole_0(A_87, B_88), A_87))), inference(superposition, [status(thm), theory('equality')], [c_352, c_304])).
% 3.38/1.58  tff(c_377, plain, (![A_87, B_88]: (k2_xboole_0(k2_xboole_0(A_87, B_88), k2_xboole_0(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_355])).
% 3.38/1.58  tff(c_833, plain, (![A_135, B_136]: (k2_xboole_0(k2_tarski(A_135, B_136), k2_xboole_0(k2_tarski(A_135, B_136), k1_tarski(A_135)))=k2_xboole_0(k2_tarski(A_135, B_136), k1_tarski(A_135)))), inference(superposition, [status(thm), theory('equality')], [c_827, c_377])).
% 3.38/1.58  tff(c_874, plain, (![A_137, B_138]: (k2_enumset1(A_137, B_138, A_137, B_138)=k2_tarski(A_137, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_36, c_708, c_833])).
% 3.38/1.58  tff(c_884, plain, (![B_138]: (k1_enumset1(B_138, B_138, B_138)=k2_tarski(B_138, B_138))), inference(superposition, [status(thm), theory('equality')], [c_874, c_44])).
% 3.38/1.58  tff(c_896, plain, (![B_139]: (k1_enumset1(B_139, B_139, B_139)=k1_tarski(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_884])).
% 3.38/1.58  tff(c_12, plain, (![E_16, C_12, B_11, A_10]: (E_16=C_12 | E_16=B_11 | E_16=A_10 | ~r2_hidden(E_16, k1_enumset1(A_10, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.58  tff(c_2555, plain, (![E_228, B_229]: (E_228=B_229 | E_228=B_229 | E_228=B_229 | ~r2_hidden(E_228, k1_tarski(B_229)))), inference(superposition, [status(thm), theory('equality')], [c_896, c_12])).
% 3.38/1.58  tff(c_2562, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1176, c_2555])).
% 3.38/1.58  tff(c_2570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_2562])).
% 3.38/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.58  
% 3.38/1.58  Inference rules
% 3.38/1.58  ----------------------
% 3.38/1.58  #Ref     : 0
% 3.38/1.58  #Sup     : 608
% 3.38/1.58  #Fact    : 0
% 3.38/1.58  #Define  : 0
% 3.38/1.58  #Split   : 0
% 3.38/1.58  #Chain   : 0
% 3.38/1.58  #Close   : 0
% 3.38/1.58  
% 3.38/1.58  Ordering : KBO
% 3.38/1.58  
% 3.38/1.58  Simplification rules
% 3.38/1.58  ----------------------
% 3.38/1.58  #Subsume      : 0
% 3.38/1.58  #Demod        : 632
% 3.38/1.58  #Tautology    : 505
% 3.38/1.58  #SimpNegUnit  : 7
% 3.38/1.58  #BackRed      : 1
% 3.38/1.58  
% 3.38/1.58  #Partial instantiations: 0
% 3.38/1.58  #Strategies tried      : 1
% 3.38/1.58  
% 3.38/1.58  Timing (in seconds)
% 3.38/1.58  ----------------------
% 3.38/1.58  Preprocessing        : 0.32
% 3.38/1.58  Parsing              : 0.17
% 3.38/1.58  CNF conversion       : 0.02
% 3.38/1.58  Main loop            : 0.54
% 3.38/1.58  Inferencing          : 0.18
% 3.38/1.58  Reduction            : 0.23
% 3.38/1.58  Demodulation         : 0.18
% 3.38/1.58  BG Simplification    : 0.02
% 3.38/1.58  Subsumption          : 0.08
% 3.38/1.58  Abstraction          : 0.03
% 3.38/1.58  MUC search           : 0.00
% 3.38/1.58  Cooper               : 0.00
% 3.38/1.58  Total                : 0.90
% 3.38/1.58  Index Insertion      : 0.00
% 3.38/1.58  Index Deletion       : 0.00
% 3.38/1.58  Index Matching       : 0.00
% 3.38/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
