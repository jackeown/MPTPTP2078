%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 6.91s
% Output     : CNFRefutation 6.91s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 149 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 132 expanded)
%              Number of equality atoms :   48 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_34,plain,(
    ! [A_64,B_65,C_66] : k2_enumset1(A_64,A_64,B_65,C_66) = k1_enumset1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_26,C_28,B_27,D_29] : k2_enumset1(A_26,C_28,B_27,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_67,B_68,C_69,D_70] : k3_enumset1(A_67,A_67,B_68,C_69,D_70) = k2_enumset1(A_67,B_68,C_69,D_70) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1494,plain,(
    ! [C_152,D_151,A_150,B_153,E_154] : k2_xboole_0(k1_enumset1(A_150,B_153,C_152),k2_tarski(D_151,E_154)) = k3_enumset1(A_150,B_153,C_152,D_151,E_154) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1518,plain,(
    ! [A_62,B_63,D_151,E_154] : k3_enumset1(A_62,A_62,B_63,D_151,E_154) = k2_xboole_0(k2_tarski(A_62,B_63),k2_tarski(D_151,E_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1494])).

tff(c_1524,plain,(
    ! [A_62,B_63,D_151,E_154] : k2_xboole_0(k2_tarski(A_62,B_63),k2_tarski(D_151,E_154)) = k2_enumset1(A_62,B_63,D_151,E_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1518])).

tff(c_30,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1326,plain,(
    ! [A_138,B_139,C_140,D_141] : k2_xboole_0(k1_enumset1(A_138,B_139,C_140),k1_tarski(D_141)) = k2_enumset1(A_138,B_139,C_140,D_141) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1350,plain,(
    ! [A_62,B_63,D_141] : k2_xboole_0(k2_tarski(A_62,B_63),k1_tarski(D_141)) = k2_enumset1(A_62,A_62,B_63,D_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1326])).

tff(c_5320,plain,(
    ! [A_229,B_230,D_231] : k2_xboole_0(k2_tarski(A_229,B_230),k1_tarski(D_231)) = k1_enumset1(A_229,B_230,D_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1350])).

tff(c_5341,plain,(
    ! [A_61,D_231] : k2_xboole_0(k1_tarski(A_61),k1_tarski(D_231)) = k1_enumset1(A_61,A_61,D_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5320])).

tff(c_5345,plain,(
    ! [A_232,D_233] : k2_xboole_0(k1_tarski(A_232),k1_tarski(D_233)) = k2_tarski(A_232,D_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5341])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_942,plain,(
    ! [A_123,B_124] : k5_xboole_0(k5_xboole_0(A_123,B_124),k3_xboole_0(A_123,B_124)) = k2_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4293,plain,(
    ! [A_213,B_214] : k5_xboole_0(k5_xboole_0(A_213,B_214),k3_xboole_0(B_214,A_213)) = k2_xboole_0(B_214,A_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_942])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4315,plain,(
    ! [A_213,B_214] : k5_xboole_0(A_213,k5_xboole_0(B_214,k3_xboole_0(B_214,A_213))) = k2_xboole_0(B_214,A_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_4293,c_6])).

tff(c_4365,plain,(
    ! [B_214,A_213] : k2_xboole_0(B_214,A_213) = k2_xboole_0(A_213,B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_4315])).

tff(c_5366,plain,(
    ! [D_234,A_235] : k2_xboole_0(k1_tarski(D_234),k1_tarski(A_235)) = k2_tarski(A_235,D_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_5345,c_4365])).

tff(c_5344,plain,(
    ! [A_61,D_231] : k2_xboole_0(k1_tarski(A_61),k1_tarski(D_231)) = k2_tarski(A_61,D_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5341])).

tff(c_5372,plain,(
    ! [D_234,A_235] : k2_tarski(D_234,A_235) = k2_tarski(A_235,D_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_5366,c_5344])).

tff(c_206,plain,(
    ! [A_95,D_96,C_97,B_98] : k2_enumset1(A_95,D_96,C_97,B_98) = k2_enumset1(A_95,B_98,C_97,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_291,plain,(
    ! [B_99,D_100,C_101] : k2_enumset1(B_99,D_100,C_101,B_99) = k1_enumset1(B_99,C_101,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_34])).

tff(c_996,plain,(
    ! [D_125,B_126,C_127] : k2_enumset1(D_125,B_126,C_127,D_125) = k1_enumset1(D_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_291])).

tff(c_242,plain,(
    ! [B_98,D_96,C_97] : k2_enumset1(B_98,D_96,C_97,B_98) = k1_enumset1(B_98,C_97,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_34])).

tff(c_1022,plain,(
    ! [D_125,C_127,B_126] : k1_enumset1(D_125,C_127,B_126) = k1_enumset1(D_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_242])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1115,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_40])).

tff(c_4371,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4365,c_1115])).

tff(c_5398,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5372,c_5372,c_4371])).

tff(c_7328,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_5398])).

tff(c_7331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_7328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.91/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.40  
% 6.91/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.40  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.91/2.40  
% 6.91/2.40  %Foreground sorts:
% 6.91/2.40  
% 6.91/2.40  
% 6.91/2.40  %Background operators:
% 6.91/2.40  
% 6.91/2.40  
% 6.91/2.40  %Foreground operators:
% 6.91/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.91/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.91/2.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.91/2.40  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.91/2.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.91/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.91/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.91/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.91/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.91/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.91/2.40  tff('#skF_1', type, '#skF_1': $i).
% 6.91/2.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.91/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.91/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.91/2.40  
% 6.91/2.42  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.91/2.42  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 6.91/2.42  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.91/2.42  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.91/2.42  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 6.91/2.42  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.91/2.42  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 6.91/2.42  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.91/2.42  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.91/2.42  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.91/2.42  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.91/2.42  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.91/2.42  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 6.91/2.42  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 6.91/2.42  tff(c_34, plain, (![A_64, B_65, C_66]: (k2_enumset1(A_64, A_64, B_65, C_66)=k1_enumset1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.91/2.42  tff(c_16, plain, (![A_26, C_28, B_27, D_29]: (k2_enumset1(A_26, C_28, B_27, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.91/2.42  tff(c_36, plain, (![A_67, B_68, C_69, D_70]: (k3_enumset1(A_67, A_67, B_68, C_69, D_70)=k2_enumset1(A_67, B_68, C_69, D_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.91/2.42  tff(c_32, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.91/2.42  tff(c_1494, plain, (![C_152, D_151, A_150, B_153, E_154]: (k2_xboole_0(k1_enumset1(A_150, B_153, C_152), k2_tarski(D_151, E_154))=k3_enumset1(A_150, B_153, C_152, D_151, E_154))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.91/2.42  tff(c_1518, plain, (![A_62, B_63, D_151, E_154]: (k3_enumset1(A_62, A_62, B_63, D_151, E_154)=k2_xboole_0(k2_tarski(A_62, B_63), k2_tarski(D_151, E_154)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1494])).
% 6.91/2.42  tff(c_1524, plain, (![A_62, B_63, D_151, E_154]: (k2_xboole_0(k2_tarski(A_62, B_63), k2_tarski(D_151, E_154))=k2_enumset1(A_62, B_63, D_151, E_154))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1518])).
% 6.91/2.42  tff(c_30, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.91/2.42  tff(c_1326, plain, (![A_138, B_139, C_140, D_141]: (k2_xboole_0(k1_enumset1(A_138, B_139, C_140), k1_tarski(D_141))=k2_enumset1(A_138, B_139, C_140, D_141))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.91/2.42  tff(c_1350, plain, (![A_62, B_63, D_141]: (k2_xboole_0(k2_tarski(A_62, B_63), k1_tarski(D_141))=k2_enumset1(A_62, A_62, B_63, D_141))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1326])).
% 6.91/2.42  tff(c_5320, plain, (![A_229, B_230, D_231]: (k2_xboole_0(k2_tarski(A_229, B_230), k1_tarski(D_231))=k1_enumset1(A_229, B_230, D_231))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1350])).
% 6.91/2.42  tff(c_5341, plain, (![A_61, D_231]: (k2_xboole_0(k1_tarski(A_61), k1_tarski(D_231))=k1_enumset1(A_61, A_61, D_231))), inference(superposition, [status(thm), theory('equality')], [c_30, c_5320])).
% 6.91/2.42  tff(c_5345, plain, (![A_232, D_233]: (k2_xboole_0(k1_tarski(A_232), k1_tarski(D_233))=k2_tarski(A_232, D_233))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5341])).
% 6.91/2.42  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.91/2.42  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.91/2.42  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.91/2.42  tff(c_942, plain, (![A_123, B_124]: (k5_xboole_0(k5_xboole_0(A_123, B_124), k3_xboole_0(A_123, B_124))=k2_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.42  tff(c_4293, plain, (![A_213, B_214]: (k5_xboole_0(k5_xboole_0(A_213, B_214), k3_xboole_0(B_214, A_213))=k2_xboole_0(B_214, A_213))), inference(superposition, [status(thm), theory('equality')], [c_2, c_942])).
% 6.91/2.42  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.91/2.42  tff(c_4315, plain, (![A_213, B_214]: (k5_xboole_0(A_213, k5_xboole_0(B_214, k3_xboole_0(B_214, A_213)))=k2_xboole_0(B_214, A_213))), inference(superposition, [status(thm), theory('equality')], [c_4293, c_6])).
% 6.91/2.42  tff(c_4365, plain, (![B_214, A_213]: (k2_xboole_0(B_214, A_213)=k2_xboole_0(A_213, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_4315])).
% 6.91/2.42  tff(c_5366, plain, (![D_234, A_235]: (k2_xboole_0(k1_tarski(D_234), k1_tarski(A_235))=k2_tarski(A_235, D_234))), inference(superposition, [status(thm), theory('equality')], [c_5345, c_4365])).
% 6.91/2.42  tff(c_5344, plain, (![A_61, D_231]: (k2_xboole_0(k1_tarski(A_61), k1_tarski(D_231))=k2_tarski(A_61, D_231))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5341])).
% 6.91/2.42  tff(c_5372, plain, (![D_234, A_235]: (k2_tarski(D_234, A_235)=k2_tarski(A_235, D_234))), inference(superposition, [status(thm), theory('equality')], [c_5366, c_5344])).
% 6.91/2.42  tff(c_206, plain, (![A_95, D_96, C_97, B_98]: (k2_enumset1(A_95, D_96, C_97, B_98)=k2_enumset1(A_95, B_98, C_97, D_96))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.91/2.42  tff(c_291, plain, (![B_99, D_100, C_101]: (k2_enumset1(B_99, D_100, C_101, B_99)=k1_enumset1(B_99, C_101, D_100))), inference(superposition, [status(thm), theory('equality')], [c_206, c_34])).
% 6.91/2.42  tff(c_996, plain, (![D_125, B_126, C_127]: (k2_enumset1(D_125, B_126, C_127, D_125)=k1_enumset1(D_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_16, c_291])).
% 6.91/2.42  tff(c_242, plain, (![B_98, D_96, C_97]: (k2_enumset1(B_98, D_96, C_97, B_98)=k1_enumset1(B_98, C_97, D_96))), inference(superposition, [status(thm), theory('equality')], [c_206, c_34])).
% 6.91/2.42  tff(c_1022, plain, (![D_125, C_127, B_126]: (k1_enumset1(D_125, C_127, B_126)=k1_enumset1(D_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_996, c_242])).
% 6.91/2.42  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.91/2.42  tff(c_1115, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_40])).
% 6.91/2.42  tff(c_4371, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4365, c_1115])).
% 6.91/2.42  tff(c_5398, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5372, c_5372, c_4371])).
% 6.91/2.42  tff(c_7328, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_5398])).
% 6.91/2.42  tff(c_7331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_7328])).
% 6.91/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.42  
% 6.91/2.42  Inference rules
% 6.91/2.42  ----------------------
% 6.91/2.42  #Ref     : 0
% 6.91/2.42  #Sup     : 1896
% 6.91/2.42  #Fact    : 0
% 6.91/2.42  #Define  : 0
% 6.91/2.42  #Split   : 0
% 6.91/2.42  #Chain   : 0
% 6.91/2.42  #Close   : 0
% 6.91/2.42  
% 6.91/2.42  Ordering : KBO
% 6.91/2.42  
% 6.91/2.42  Simplification rules
% 6.91/2.42  ----------------------
% 6.91/2.42  #Subsume      : 436
% 6.91/2.42  #Demod        : 968
% 6.91/2.42  #Tautology    : 949
% 6.91/2.42  #SimpNegUnit  : 0
% 6.91/2.42  #BackRed      : 5
% 6.91/2.42  
% 6.91/2.42  #Partial instantiations: 0
% 6.91/2.42  #Strategies tried      : 1
% 6.91/2.42  
% 6.91/2.42  Timing (in seconds)
% 6.91/2.42  ----------------------
% 6.91/2.42  Preprocessing        : 0.35
% 6.91/2.42  Parsing              : 0.18
% 6.91/2.42  CNF conversion       : 0.02
% 6.91/2.42  Main loop            : 1.27
% 6.91/2.42  Inferencing          : 0.36
% 6.91/2.42  Reduction            : 0.66
% 6.91/2.42  Demodulation         : 0.60
% 6.91/2.42  BG Simplification    : 0.05
% 6.91/2.42  Subsumption          : 0.15
% 6.91/2.42  Abstraction          : 0.07
% 6.91/2.42  MUC search           : 0.00
% 6.91/2.42  Cooper               : 0.00
% 6.91/2.42  Total                : 1.64
% 6.91/2.42  Index Insertion      : 0.00
% 6.91/2.42  Index Deletion       : 0.00
% 6.91/2.42  Index Matching       : 0.00
% 6.91/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
