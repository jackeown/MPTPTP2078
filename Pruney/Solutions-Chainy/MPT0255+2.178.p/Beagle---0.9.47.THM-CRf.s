%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :   77 (  93 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :   62 (  79 expanded)
%              Number of equality atoms :   61 (  78 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(c_163,plain,(
    ! [C_71,B_72,A_73] : k1_enumset1(C_71,B_72,A_73) = k1_enumset1(A_73,B_72,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_179,plain,(
    ! [C_71,B_72] : k1_enumset1(C_71,B_72,B_72) = k2_tarski(B_72,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_22])).

tff(c_24,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_31,B_32,C_33,D_34] : k3_enumset1(A_31,A_31,B_32,C_33,D_34) = k2_enumset1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_35,B_36,C_37,D_38,E_39] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,E_39) = k3_enumset1(A_35,B_36,C_37,D_38,E_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45) = k4_enumset1(A_40,B_41,C_42,D_43,E_44,F_45) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_46,E_50,B_47,C_48,D_49,G_52,F_51] : k6_enumset1(A_46,A_46,B_47,C_48,D_49,E_50,F_51,G_52) = k5_enumset1(A_46,B_47,C_48,D_49,E_50,F_51,G_52) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_373,plain,(
    ! [A_86,B_87] : k5_xboole_0(k5_xboole_0(A_86,B_87),k2_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_416,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_373])).

tff(c_427,plain,(
    ! [A_88] : k5_xboole_0(k1_xboole_0,A_88) = k3_xboole_0(A_88,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_416])).

tff(c_275,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_293,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k5_xboole_0(A_81,B_82))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_12])).

tff(c_439,plain,(
    ! [A_88] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_88,k3_xboole_0(A_88,A_88))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_293])).

tff(c_470,plain,(
    ! [A_88] : k5_xboole_0(k1_xboole_0,k4_xboole_0(A_88,A_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_439])).

tff(c_327,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k5_xboole_0(B_85,k5_xboole_0(A_84,B_85))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_12])).

tff(c_530,plain,(
    ! [A_94] : k5_xboole_0(A_94,k5_xboole_0(k1_xboole_0,A_94)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_327])).

tff(c_595,plain,(
    ! [A_95] : k5_xboole_0(k4_xboole_0(A_95,A_95),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_530])).

tff(c_603,plain,(
    ! [A_95] : k5_xboole_0(k4_xboole_0(A_95,A_95),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_293])).

tff(c_622,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12,c_603])).

tff(c_36,plain,(
    ! [B_56] : k4_xboole_0(k1_tarski(B_56),k1_tarski(B_56)) != k1_tarski(B_56) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_630,plain,(
    ! [B_56] : k1_tarski(B_56) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_36])).

tff(c_1970,plain,(
    ! [C_137,D_141,A_138,G_143,H_144,E_142,F_140,B_139] : k2_xboole_0(k1_tarski(A_138),k5_enumset1(B_139,C_137,D_141,E_142,F_140,G_143,H_144)) = k6_enumset1(A_138,B_139,C_137,D_141,E_142,F_140,G_143,H_144) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | k2_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1979,plain,(
    ! [C_137,D_141,A_138,G_143,H_144,E_142,F_140,B_139] :
      ( k1_tarski(A_138) = k1_xboole_0
      | k6_enumset1(A_138,B_139,C_137,D_141,E_142,F_140,G_143,H_144) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_6])).

tff(c_2350,plain,(
    ! [D_149,E_151,C_147,H_154,G_148,A_150,B_153,F_152] : k6_enumset1(A_150,B_153,C_147,D_149,E_151,F_152,G_148,H_154) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_1979])).

tff(c_6459,plain,(
    ! [D_227,A_230,G_231,E_228,B_225,C_229,F_226] : k5_enumset1(A_230,B_225,C_229,D_227,E_228,F_226,G_231) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2350])).

tff(c_6462,plain,(
    ! [B_237,F_235,A_233,D_234,C_236,E_232] : k4_enumset1(A_233,B_237,C_236,D_234,E_232,F_235) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6459])).

tff(c_6465,plain,(
    ! [B_242,C_239,E_240,D_241,A_238] : k3_enumset1(A_238,B_242,C_239,D_241,E_240) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6462])).

tff(c_6469,plain,(
    ! [A_243,B_244,C_245,D_246] : k2_enumset1(A_243,B_244,C_245,D_246) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6465])).

tff(c_6472,plain,(
    ! [A_247,B_248,C_249] : k1_enumset1(A_247,B_248,C_249) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6469])).

tff(c_6474,plain,(
    ! [B_72,C_71] : k2_tarski(B_72,C_71) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_6472])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    ! [A_61,B_62] :
      ( k1_xboole_0 = A_61
      | k2_xboole_0(A_61,B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_6482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6474,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.30  
% 5.82/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.82/2.30  
% 5.82/2.30  %Foreground sorts:
% 5.82/2.30  
% 5.82/2.30  
% 5.82/2.30  %Background operators:
% 5.82/2.30  
% 5.82/2.30  
% 5.82/2.30  %Foreground operators:
% 5.82/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.82/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.82/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.82/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.82/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.82/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.82/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.82/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.82/2.30  tff('#skF_2', type, '#skF_2': $i).
% 5.82/2.30  tff('#skF_3', type, '#skF_3': $i).
% 5.82/2.30  tff('#skF_1', type, '#skF_1': $i).
% 5.82/2.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.82/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.82/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.82/2.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.30  
% 6.22/2.32  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 6.22/2.32  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.22/2.32  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.22/2.32  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.22/2.32  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.22/2.32  tff(f_57, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.22/2.32  tff(f_59, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 6.22/2.32  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.22/2.32  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.22/2.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.22/2.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.22/2.32  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.22/2.32  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.22/2.32  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.22/2.32  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 6.22/2.32  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 6.22/2.32  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 6.22/2.32  tff(c_163, plain, (![C_71, B_72, A_73]: (k1_enumset1(C_71, B_72, A_73)=k1_enumset1(A_73, B_72, C_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.22/2.32  tff(c_22, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.22/2.32  tff(c_179, plain, (![C_71, B_72]: (k1_enumset1(C_71, B_72, B_72)=k2_tarski(B_72, C_71))), inference(superposition, [status(thm), theory('equality')], [c_163, c_22])).
% 6.22/2.32  tff(c_24, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.22/2.32  tff(c_26, plain, (![A_31, B_32, C_33, D_34]: (k3_enumset1(A_31, A_31, B_32, C_33, D_34)=k2_enumset1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.32  tff(c_28, plain, (![A_35, B_36, C_37, D_38, E_39]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, E_39)=k3_enumset1(A_35, B_36, C_37, D_38, E_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.22/2.32  tff(c_30, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45)=k4_enumset1(A_40, B_41, C_42, D_43, E_44, F_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.22/2.32  tff(c_32, plain, (![A_46, E_50, B_47, C_48, D_49, G_52, F_51]: (k6_enumset1(A_46, A_46, B_47, C_48, D_49, E_50, F_51, G_52)=k5_enumset1(A_46, B_47, C_48, D_49, E_50, F_51, G_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.22/2.32  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.22/2.32  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.22/2.32  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.22/2.32  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.22/2.32  tff(c_373, plain, (![A_86, B_87]: (k5_xboole_0(k5_xboole_0(A_86, B_87), k2_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.22/2.32  tff(c_416, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_373])).
% 6.22/2.32  tff(c_427, plain, (![A_88]: (k5_xboole_0(k1_xboole_0, A_88)=k3_xboole_0(A_88, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_416])).
% 6.22/2.32  tff(c_275, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.22/2.32  tff(c_293, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k5_xboole_0(A_81, B_82)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_275, c_12])).
% 6.22/2.32  tff(c_439, plain, (![A_88]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_88, k3_xboole_0(A_88, A_88)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_427, c_293])).
% 6.22/2.32  tff(c_470, plain, (![A_88]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(A_88, A_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_439])).
% 6.22/2.32  tff(c_327, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k5_xboole_0(B_85, k5_xboole_0(A_84, B_85)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_275, c_12])).
% 6.22/2.32  tff(c_530, plain, (![A_94]: (k5_xboole_0(A_94, k5_xboole_0(k1_xboole_0, A_94))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_327])).
% 6.22/2.32  tff(c_595, plain, (![A_95]: (k5_xboole_0(k4_xboole_0(A_95, A_95), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_470, c_530])).
% 6.22/2.32  tff(c_603, plain, (![A_95]: (k5_xboole_0(k4_xboole_0(A_95, A_95), k5_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_595, c_293])).
% 6.22/2.32  tff(c_622, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12, c_603])).
% 6.22/2.32  tff(c_36, plain, (![B_56]: (k4_xboole_0(k1_tarski(B_56), k1_tarski(B_56))!=k1_tarski(B_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.22/2.32  tff(c_630, plain, (![B_56]: (k1_tarski(B_56)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_622, c_36])).
% 6.22/2.32  tff(c_1970, plain, (![C_137, D_141, A_138, G_143, H_144, E_142, F_140, B_139]: (k2_xboole_0(k1_tarski(A_138), k5_enumset1(B_139, C_137, D_141, E_142, F_140, G_143, H_144))=k6_enumset1(A_138, B_139, C_137, D_141, E_142, F_140, G_143, H_144))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.22/2.32  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | k2_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.22/2.32  tff(c_1979, plain, (![C_137, D_141, A_138, G_143, H_144, E_142, F_140, B_139]: (k1_tarski(A_138)=k1_xboole_0 | k6_enumset1(A_138, B_139, C_137, D_141, E_142, F_140, G_143, H_144)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1970, c_6])).
% 6.22/2.32  tff(c_2350, plain, (![D_149, E_151, C_147, H_154, G_148, A_150, B_153, F_152]: (k6_enumset1(A_150, B_153, C_147, D_149, E_151, F_152, G_148, H_154)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_630, c_1979])).
% 6.22/2.32  tff(c_6459, plain, (![D_227, A_230, G_231, E_228, B_225, C_229, F_226]: (k5_enumset1(A_230, B_225, C_229, D_227, E_228, F_226, G_231)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_2350])).
% 6.22/2.32  tff(c_6462, plain, (![B_237, F_235, A_233, D_234, C_236, E_232]: (k4_enumset1(A_233, B_237, C_236, D_234, E_232, F_235)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_6459])).
% 6.22/2.32  tff(c_6465, plain, (![B_242, C_239, E_240, D_241, A_238]: (k3_enumset1(A_238, B_242, C_239, D_241, E_240)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_6462])).
% 6.22/2.32  tff(c_6469, plain, (![A_243, B_244, C_245, D_246]: (k2_enumset1(A_243, B_244, C_245, D_246)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_6465])).
% 6.22/2.32  tff(c_6472, plain, (![A_247, B_248, C_249]: (k1_enumset1(A_247, B_248, C_249)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_6469])).
% 6.22/2.32  tff(c_6474, plain, (![B_72, C_71]: (k2_tarski(B_72, C_71)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_6472])).
% 6.22/2.32  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.22/2.32  tff(c_89, plain, (![A_61, B_62]: (k1_xboole_0=A_61 | k2_xboole_0(A_61, B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.22/2.32  tff(c_96, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_89])).
% 6.22/2.32  tff(c_6482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6474, c_96])).
% 6.22/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.32  
% 6.22/2.32  Inference rules
% 6.22/2.32  ----------------------
% 6.22/2.32  #Ref     : 0
% 6.22/2.32  #Sup     : 1639
% 6.22/2.32  #Fact    : 0
% 6.22/2.32  #Define  : 0
% 6.22/2.32  #Split   : 1
% 6.22/2.32  #Chain   : 0
% 6.22/2.32  #Close   : 0
% 6.22/2.32  
% 6.22/2.32  Ordering : KBO
% 6.22/2.32  
% 6.22/2.32  Simplification rules
% 6.22/2.32  ----------------------
% 6.22/2.32  #Subsume      : 14
% 6.22/2.32  #Demod        : 1600
% 6.22/2.32  #Tautology    : 869
% 6.22/2.32  #SimpNegUnit  : 5
% 6.22/2.32  #BackRed      : 16
% 6.22/2.32  
% 6.22/2.32  #Partial instantiations: 0
% 6.22/2.32  #Strategies tried      : 1
% 6.22/2.32  
% 6.22/2.32  Timing (in seconds)
% 6.22/2.32  ----------------------
% 6.22/2.32  Preprocessing        : 0.32
% 6.22/2.32  Parsing              : 0.17
% 6.22/2.32  CNF conversion       : 0.02
% 6.22/2.32  Main loop            : 1.23
% 6.22/2.32  Inferencing          : 0.35
% 6.22/2.32  Reduction            : 0.61
% 6.22/2.32  Demodulation         : 0.52
% 6.22/2.32  BG Simplification    : 0.05
% 6.22/2.32  Subsumption          : 0.16
% 6.22/2.32  Abstraction          : 0.08
% 6.22/2.32  MUC search           : 0.00
% 6.22/2.32  Cooper               : 0.00
% 6.22/2.32  Total                : 1.58
% 6.22/2.32  Index Insertion      : 0.00
% 6.22/2.32  Index Deletion       : 0.00
% 6.22/2.32  Index Matching       : 0.00
% 6.22/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
