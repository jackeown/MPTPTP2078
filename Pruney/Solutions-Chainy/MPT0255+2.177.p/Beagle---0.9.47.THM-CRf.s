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
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   77 (  80 expanded)
%              Number of leaves         :   39 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 (  65 expanded)
%              Number of equality atoms :   60 (  64 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(c_167,plain,(
    ! [B_84,C_85,A_86] : k1_enumset1(B_84,C_85,A_86) = k1_enumset1(A_86,B_84,C_85) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [A_86,C_85] : k1_enumset1(A_86,C_85,C_85) = k2_tarski(C_85,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_26])).

tff(c_321,plain,(
    ! [A_96,B_97,D_98,C_99] : k2_enumset1(A_96,B_97,D_98,C_99) = k2_enumset1(A_96,B_97,C_99,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_337,plain,(
    ! [B_97,D_98,C_99] : k2_enumset1(B_97,B_97,D_98,C_99) = k1_enumset1(B_97,C_99,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_28])).

tff(c_30,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [B_49,A_48,D_51,E_52,C_50] : k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52) = k3_enumset1(A_48,B_49,C_50,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_53,D_56,E_57,C_55,F_58,B_54] : k5_enumset1(A_53,A_53,B_54,C_55,D_56,E_57,F_58) = k4_enumset1(A_53,B_54,C_55,D_56,E_57,F_58) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [F_64,D_62,A_59,G_65,C_61,E_63,B_60] : k6_enumset1(A_59,A_59,B_60,C_61,D_62,E_63,F_64,G_65) = k5_enumset1(A_59,B_60,C_61,D_62,E_63,F_64,G_65) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_494,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_546,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k5_xboole_0(B_110,k5_xboole_0(A_109,B_110))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_12])).

tff(c_580,plain,(
    ! [A_7] : k5_xboole_0(A_7,k5_xboole_0(k1_xboole_0,A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_546])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_819,plain,(
    ! [A_115,B_116] : k5_xboole_0(k5_xboole_0(A_115,B_116),k2_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_871,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_819])).

tff(c_882,plain,(
    ! [A_117] : k5_xboole_0(k1_xboole_0,A_117) = k3_xboole_0(A_117,A_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_871])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_909,plain,(
    ! [A_117] : k5_xboole_0(A_117,k5_xboole_0(k1_xboole_0,A_117)) = k4_xboole_0(A_117,A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_4])).

tff(c_935,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_909])).

tff(c_40,plain,(
    ! [B_69] : k4_xboole_0(k1_tarski(B_69),k1_tarski(B_69)) != k1_tarski(B_69) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_938,plain,(
    ! [B_69] : k1_tarski(B_69) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_40])).

tff(c_2174,plain,(
    ! [F_163,C_161,E_165,D_166,G_167,H_160,A_164,B_162] : k2_xboole_0(k1_tarski(A_164),k5_enumset1(B_162,C_161,D_166,E_165,F_163,G_167,H_160)) = k6_enumset1(A_164,B_162,C_161,D_166,E_165,F_163,G_167,H_160) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | k2_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2183,plain,(
    ! [F_163,C_161,E_165,D_166,G_167,H_160,A_164,B_162] :
      ( k1_tarski(A_164) = k1_xboole_0
      | k6_enumset1(A_164,B_162,C_161,D_166,E_165,F_163,G_167,H_160) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2174,c_6])).

tff(c_3594,plain,(
    ! [A_207,D_205,B_204,E_211,F_206,H_210,C_208,G_209] : k6_enumset1(A_207,B_204,C_208,D_205,E_211,F_206,G_209,H_210) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_938,c_2183])).

tff(c_5188,plain,(
    ! [B_250,G_248,C_247,E_253,F_251,A_249,D_252] : k5_enumset1(A_249,B_250,C_247,D_252,E_253,F_251,G_248) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3594])).

tff(c_5192,plain,(
    ! [D_257,E_256,A_255,B_258,F_259,C_254] : k4_enumset1(A_255,B_258,C_254,D_257,E_256,F_259) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5188])).

tff(c_5195,plain,(
    ! [B_261,C_263,D_260,E_264,A_262] : k3_enumset1(A_262,B_261,C_263,D_260,E_264) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5192])).

tff(c_5198,plain,(
    ! [A_265,B_266,C_267,D_268] : k2_enumset1(A_265,B_266,C_267,D_268) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5195])).

tff(c_5207,plain,(
    ! [B_269,C_270,D_271] : k1_enumset1(B_269,C_270,D_271) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_5198])).

tff(c_5221,plain,(
    ! [C_85,A_86] : k2_tarski(C_85,A_86) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_5207])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    ! [A_74,B_75] :
      ( k1_xboole_0 = A_74
      | k2_xboole_0(A_74,B_75) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_93])).

tff(c_5231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5221,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.99  
% 4.95/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.99  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.95/1.99  
% 4.95/1.99  %Foreground sorts:
% 4.95/1.99  
% 4.95/1.99  
% 4.95/1.99  %Background operators:
% 4.95/1.99  
% 4.95/1.99  
% 4.95/1.99  %Foreground operators:
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.95/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.95/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.95/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.95/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.95/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.95/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.95/1.99  
% 4.95/2.00  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 4.95/2.00  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.95/2.00  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 4.95/2.00  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.95/2.00  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.95/2.00  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.95/2.00  tff(f_61, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.95/2.00  tff(f_63, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.95/2.00  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.95/2.00  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.95/2.00  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.95/2.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.95/2.00  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.95/2.00  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.95/2.00  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.95/2.00  tff(f_49, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 4.95/2.00  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 4.95/2.00  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 4.95/2.00  tff(c_167, plain, (![B_84, C_85, A_86]: (k1_enumset1(B_84, C_85, A_86)=k1_enumset1(A_86, B_84, C_85))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.95/2.00  tff(c_26, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.95/2.00  tff(c_187, plain, (![A_86, C_85]: (k1_enumset1(A_86, C_85, C_85)=k2_tarski(C_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_167, c_26])).
% 4.95/2.00  tff(c_321, plain, (![A_96, B_97, D_98, C_99]: (k2_enumset1(A_96, B_97, D_98, C_99)=k2_enumset1(A_96, B_97, C_99, D_98))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.95/2.00  tff(c_28, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.95/2.00  tff(c_337, plain, (![B_97, D_98, C_99]: (k2_enumset1(B_97, B_97, D_98, C_99)=k1_enumset1(B_97, C_99, D_98))), inference(superposition, [status(thm), theory('equality')], [c_321, c_28])).
% 4.95/2.00  tff(c_30, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.95/2.00  tff(c_32, plain, (![B_49, A_48, D_51, E_52, C_50]: (k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52)=k3_enumset1(A_48, B_49, C_50, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.95/2.00  tff(c_34, plain, (![A_53, D_56, E_57, C_55, F_58, B_54]: (k5_enumset1(A_53, A_53, B_54, C_55, D_56, E_57, F_58)=k4_enumset1(A_53, B_54, C_55, D_56, E_57, F_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.95/2.00  tff(c_36, plain, (![F_64, D_62, A_59, G_65, C_61, E_63, B_60]: (k6_enumset1(A_59, A_59, B_60, C_61, D_62, E_63, F_64, G_65)=k5_enumset1(A_59, B_60, C_61, D_62, E_63, F_64, G_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.95/2.00  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.95/2.00  tff(c_494, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.95/2.00  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.95/2.00  tff(c_546, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k5_xboole_0(B_110, k5_xboole_0(A_109, B_110)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_494, c_12])).
% 4.95/2.00  tff(c_580, plain, (![A_7]: (k5_xboole_0(A_7, k5_xboole_0(k1_xboole_0, A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_546])).
% 4.95/2.00  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.95/2.00  tff(c_819, plain, (![A_115, B_116]: (k5_xboole_0(k5_xboole_0(A_115, B_116), k2_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.95/2.00  tff(c_871, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_819])).
% 4.95/2.00  tff(c_882, plain, (![A_117]: (k5_xboole_0(k1_xboole_0, A_117)=k3_xboole_0(A_117, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_871])).
% 4.95/2.00  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.95/2.00  tff(c_909, plain, (![A_117]: (k5_xboole_0(A_117, k5_xboole_0(k1_xboole_0, A_117))=k4_xboole_0(A_117, A_117))), inference(superposition, [status(thm), theory('equality')], [c_882, c_4])).
% 4.95/2.00  tff(c_935, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_580, c_909])).
% 4.95/2.00  tff(c_40, plain, (![B_69]: (k4_xboole_0(k1_tarski(B_69), k1_tarski(B_69))!=k1_tarski(B_69))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.95/2.00  tff(c_938, plain, (![B_69]: (k1_tarski(B_69)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_935, c_40])).
% 4.95/2.00  tff(c_2174, plain, (![F_163, C_161, E_165, D_166, G_167, H_160, A_164, B_162]: (k2_xboole_0(k1_tarski(A_164), k5_enumset1(B_162, C_161, D_166, E_165, F_163, G_167, H_160))=k6_enumset1(A_164, B_162, C_161, D_166, E_165, F_163, G_167, H_160))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.95/2.00  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | k2_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.95/2.00  tff(c_2183, plain, (![F_163, C_161, E_165, D_166, G_167, H_160, A_164, B_162]: (k1_tarski(A_164)=k1_xboole_0 | k6_enumset1(A_164, B_162, C_161, D_166, E_165, F_163, G_167, H_160)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2174, c_6])).
% 4.95/2.00  tff(c_3594, plain, (![A_207, D_205, B_204, E_211, F_206, H_210, C_208, G_209]: (k6_enumset1(A_207, B_204, C_208, D_205, E_211, F_206, G_209, H_210)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_938, c_2183])).
% 4.95/2.00  tff(c_5188, plain, (![B_250, G_248, C_247, E_253, F_251, A_249, D_252]: (k5_enumset1(A_249, B_250, C_247, D_252, E_253, F_251, G_248)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_3594])).
% 4.95/2.00  tff(c_5192, plain, (![D_257, E_256, A_255, B_258, F_259, C_254]: (k4_enumset1(A_255, B_258, C_254, D_257, E_256, F_259)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_5188])).
% 4.95/2.00  tff(c_5195, plain, (![B_261, C_263, D_260, E_264, A_262]: (k3_enumset1(A_262, B_261, C_263, D_260, E_264)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_5192])).
% 4.95/2.00  tff(c_5198, plain, (![A_265, B_266, C_267, D_268]: (k2_enumset1(A_265, B_266, C_267, D_268)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_5195])).
% 4.95/2.00  tff(c_5207, plain, (![B_269, C_270, D_271]: (k1_enumset1(B_269, C_270, D_271)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_337, c_5198])).
% 4.95/2.00  tff(c_5221, plain, (![C_85, A_86]: (k2_tarski(C_85, A_86)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_187, c_5207])).
% 4.95/2.00  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.95/2.00  tff(c_93, plain, (![A_74, B_75]: (k1_xboole_0=A_74 | k2_xboole_0(A_74, B_75)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.95/2.00  tff(c_100, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44, c_93])).
% 4.95/2.00  tff(c_5231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5221, c_100])).
% 4.95/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/2.00  
% 4.95/2.00  Inference rules
% 4.95/2.00  ----------------------
% 4.95/2.00  #Ref     : 0
% 4.95/2.00  #Sup     : 1308
% 4.95/2.00  #Fact    : 0
% 4.95/2.00  #Define  : 0
% 4.95/2.00  #Split   : 1
% 4.95/2.00  #Chain   : 0
% 4.95/2.00  #Close   : 0
% 4.95/2.00  
% 4.95/2.00  Ordering : KBO
% 4.95/2.00  
% 4.95/2.00  Simplification rules
% 4.95/2.00  ----------------------
% 4.95/2.00  #Subsume      : 72
% 4.95/2.00  #Demod        : 1041
% 4.95/2.00  #Tautology    : 851
% 4.95/2.00  #SimpNegUnit  : 5
% 4.95/2.00  #BackRed      : 13
% 4.95/2.00  
% 4.95/2.00  #Partial instantiations: 0
% 4.95/2.00  #Strategies tried      : 1
% 4.95/2.00  
% 4.95/2.00  Timing (in seconds)
% 4.95/2.00  ----------------------
% 4.95/2.01  Preprocessing        : 0.33
% 4.95/2.01  Parsing              : 0.18
% 4.95/2.01  CNF conversion       : 0.02
% 4.95/2.01  Main loop            : 0.89
% 4.95/2.01  Inferencing          : 0.29
% 4.95/2.01  Reduction            : 0.39
% 4.95/2.01  Demodulation         : 0.32
% 4.95/2.01  BG Simplification    : 0.04
% 4.95/2.01  Subsumption          : 0.13
% 4.95/2.01  Abstraction          : 0.05
% 4.95/2.01  MUC search           : 0.00
% 4.95/2.01  Cooper               : 0.00
% 4.95/2.01  Total                : 1.26
% 4.95/2.01  Index Insertion      : 0.00
% 4.95/2.01  Index Deletion       : 0.00
% 4.95/2.01  Index Matching       : 0.00
% 4.95/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
