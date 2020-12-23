%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:01 EST 2020

% Result     : Theorem 13.73s
% Output     : CNFRefutation 13.81s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 730 expanded)
%              Number of leaves         :   26 ( 252 expanded)
%              Depth                    :   17
%              Number of atoms          :  103 ( 758 expanded)
%              Number of equality atoms :  100 ( 755 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_18,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1410,plain,(
    ! [F_124,E_122,A_123,D_121,B_120,C_119] : k2_xboole_0(k1_tarski(A_123),k3_enumset1(B_120,C_119,D_121,E_122,F_124)) = k4_enumset1(A_123,B_120,C_119,D_121,E_122,F_124) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1450,plain,(
    ! [E_138,B_137,D_141,C_136,F_139,A_140] : k4_xboole_0(k1_tarski(A_140),k4_enumset1(A_140,B_137,C_136,D_141,E_138,F_139)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_8])).

tff(c_1547,plain,(
    ! [B_144,A_145,D_143,E_147,C_146] : k4_xboole_0(k1_tarski(A_145),k3_enumset1(A_145,B_144,C_146,D_143,E_147)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1450])).

tff(c_12,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_61,C_62,B_63] : k2_xboole_0(k4_xboole_0(A_61,C_62),k4_xboole_0(B_63,C_62)) = k4_xboole_0(k2_xboole_0(A_61,B_63),C_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_233,plain,(
    ! [A_64,C_65,B_66] : k4_xboole_0(k4_xboole_0(A_64,C_65),k4_xboole_0(k2_xboole_0(A_64,B_66),C_65)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_8])).

tff(c_276,plain,(
    ! [A_15,C_65,B_16] : k4_xboole_0(k4_xboole_0(k1_tarski(A_15),C_65),k4_xboole_0(k2_tarski(A_15,B_16),C_65)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_233])).

tff(c_1552,plain,(
    ! [B_16,B_144,A_145,D_143,E_147,C_146] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_tarski(A_145,B_16),k3_enumset1(A_145,B_144,C_146,D_143,E_147))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_276])).

tff(c_854,plain,(
    ! [B_87,E_88,C_91,A_89,D_90] : k2_xboole_0(k1_enumset1(A_89,B_87,C_91),k2_tarski(D_90,E_88)) = k3_enumset1(A_89,B_87,C_91,D_90,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_875,plain,(
    ! [B_87,E_88,C_91,A_89,D_90] : k4_xboole_0(k1_enumset1(A_89,B_87,C_91),k3_enumset1(A_89,B_87,C_91,D_90,E_88)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_8])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3631,plain,(
    ! [A_193,B_194,C_195,C_196] : k4_xboole_0(k4_xboole_0(k2_tarski(A_193,B_194),C_195),k4_xboole_0(k1_enumset1(A_193,B_194,C_196),C_195)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_233])).

tff(c_4724,plain,(
    ! [D_216,B_217,C_218,A_219,E_220] : k4_xboole_0(k4_xboole_0(k2_tarski(A_219,B_217),k3_enumset1(A_219,B_217,C_218,D_216,E_220)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_3631])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | k4_xboole_0(B_2,A_1) != k4_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4747,plain,(
    ! [D_216,B_217,C_218,A_219,E_220] :
      ( k4_xboole_0(k2_tarski(A_219,B_217),k3_enumset1(A_219,B_217,C_218,D_216,E_220)) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_tarski(A_219,B_217),k3_enumset1(A_219,B_217,C_218,D_216,E_220))) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4724,c_2])).

tff(c_4760,plain,(
    ! [D_216,B_217,C_218,A_219,E_220] : k4_xboole_0(k2_tarski(A_219,B_217),k3_enumset1(A_219,B_217,C_218,D_216,E_220)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_4747])).

tff(c_3650,plain,(
    ! [B_87,E_88,C_91,A_89,D_90] : k4_xboole_0(k4_xboole_0(k2_tarski(A_89,B_87),k3_enumset1(A_89,B_87,C_91,D_90,E_88)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_3631])).

tff(c_4876,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4760,c_3650])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_219,plain,(
    ! [B_63] : k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),B_63),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_63,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_192])).

tff(c_299,plain,(
    ! [B_67] : k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),B_67),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_219])).

tff(c_337,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_299])).

tff(c_4921,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_337])).

tff(c_44,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    k2_xboole_0(k1_xboole_0,k2_tarski('#skF_1','#skF_2')) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_44])).

tff(c_982,plain,(
    ! [A_95] : k4_xboole_0(k2_xboole_0(A_95,k2_tarski('#skF_1','#skF_2')),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_95,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_192])).

tff(c_1036,plain,(
    k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_982])).

tff(c_1045,plain,(
    k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_1036])).

tff(c_1114,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k2_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_2])).

tff(c_1125,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_3'),k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1114])).

tff(c_1127,plain,(
    k2_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_3'),k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_4975,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4921,c_1127])).

tff(c_289,plain,(
    ! [A_64,B_66,B_9] : k4_xboole_0(k4_xboole_0(A_64,k2_xboole_0(k2_xboole_0(A_64,B_66),B_9)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_233])).

tff(c_358,plain,(
    ! [C_68] : k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1','#skF_2'),C_68),k4_xboole_0(k1_xboole_0,C_68)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_233])).

tff(c_3371,plain,(
    ! [C_190] : k2_xboole_0(k4_xboole_0(k1_xboole_0,C_190),k4_xboole_0(k2_tarski('#skF_1','#skF_2'),C_190)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,C_190),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_4])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] : k2_xboole_0(k4_xboole_0(A_5,C_7),k4_xboole_0(B_6,C_7)) = k4_xboole_0(k2_xboole_0(A_5,B_6),C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3398,plain,(
    ! [C_190] : k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_tarski('#skF_1','#skF_2')),C_190) = k2_xboole_0(k4_xboole_0(k1_xboole_0,C_190),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3371,c_6])).

tff(c_3475,plain,(
    ! [C_191] : k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),C_191) = k2_xboole_0(k4_xboole_0(k1_xboole_0,C_191),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3398])).

tff(c_3550,plain,(
    ! [B_9] : k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),B_9)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3475,c_8])).

tff(c_351,plain,(
    ! [A_5] : k2_xboole_0(k4_xboole_0(A_5,k1_xboole_0),k2_xboole_0(k1_xboole_0,'#skF_3')) = k4_xboole_0(k2_xboole_0(A_5,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_6])).

tff(c_6642,plain,(
    ! [A_247] : k4_xboole_0(k2_xboole_0(A_247,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_247,k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4921,c_351])).

tff(c_6708,plain,(
    ! [B_9] : k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),B_9)),k1_xboole_0),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3550,c_6642])).

tff(c_6741,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_289,c_6708])).

tff(c_6743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4975,c_6741])).

tff(c_6744,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_135,plain,(
    ! [A_59,B_60] : k2_xboole_0(k2_xboole_0(A_59,B_60),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_59,B_60),A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_171,plain,(
    ! [A_15,B_16] : k2_xboole_0(k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)),k1_xboole_0) = k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_135])).

tff(c_7584,plain,(
    ! [A_296,B_297] : k2_xboole_0(k2_tarski(A_296,B_297),k1_tarski(A_296)) = k2_xboole_0(k2_tarski(A_296,B_297),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_7634,plain,(
    ! [A_298,B_299] : k2_xboole_0(k2_tarski(A_298,B_299),k1_xboole_0) = k1_enumset1(A_298,B_299,A_298) ),
    inference(superposition,[status(thm),theory(equality)],[c_7584,c_14])).

tff(c_232,plain,(
    ! [B_63] : k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),B_63),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_219])).

tff(c_7669,plain,(
    k4_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7634,c_232])).

tff(c_7691,plain,(
    k4_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6744,c_7669])).

tff(c_7714,plain,
    ( k1_enumset1('#skF_1','#skF_2','#skF_1') = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k1_enumset1('#skF_1','#skF_2','#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7691,c_2])).

tff(c_22651,plain,(
    k4_xboole_0(k1_xboole_0,k1_enumset1('#skF_1','#skF_2','#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7714])).

tff(c_398,plain,(
    ! [B_9] : k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_xboole_0(k1_xboole_0,B_9)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_358])).

tff(c_6758,plain,(
    k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6744,c_398])).

tff(c_6778,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_37,c_6758])).

tff(c_8145,plain,(
    ! [A_313,B_314,B_315] : k4_xboole_0(k2_xboole_0(A_313,B_314),k2_xboole_0(A_313,B_315)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_314,k2_xboole_0(A_313,B_315))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_192])).

tff(c_8288,plain,(
    ! [A_17,B_18,B_314,C_19] : k4_xboole_0(k2_xboole_0(k2_tarski(A_17,B_18),B_314),k1_enumset1(A_17,B_18,C_19)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_314,k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(C_19)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8145])).

tff(c_24580,plain,(
    ! [A_560,B_561,B_562,C_563] : k4_xboole_0(k2_xboole_0(k2_tarski(A_560,B_561),B_562),k1_enumset1(A_560,B_561,C_563)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_562,k1_enumset1(A_560,B_561,C_563))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8288])).

tff(c_24903,plain,(
    ! [C_572] : k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3',k1_enumset1('#skF_1','#skF_2',C_572))) = k4_xboole_0(k1_xboole_0,k1_enumset1('#skF_1','#skF_2',C_572)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_24580])).

tff(c_7705,plain,(
    ! [B_6] : k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),B_6),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_6,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7691,c_6])).

tff(c_7724,plain,(
    ! [B_6] : k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),B_6),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7705])).

tff(c_10618,plain,(
    ! [B_358] : k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),B_358),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_358) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7705])).

tff(c_10679,plain,(
    ! [B_4] : k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_1'),B_4),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_4,k1_enumset1('#skF_1','#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10618])).

tff(c_10689,plain,(
    ! [B_4] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_4,k1_enumset1('#skF_1','#skF_2','#skF_1'))) = k2_xboole_0(k1_xboole_0,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7724,c_10679])).

tff(c_24959,plain,(
    k4_xboole_0(k1_xboole_0,k1_enumset1('#skF_1','#skF_2','#skF_1')) = k2_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24903,c_10689])).

tff(c_25028,plain,(
    k4_xboole_0(k1_xboole_0,k1_enumset1('#skF_1','#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6778,c_24959])).

tff(c_25030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22651,c_25028])).

tff(c_25031,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7714])).

tff(c_168,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(C_19)),k1_xboole_0) = k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k2_tarski(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_9368,plain,(
    ! [A_335,B_336,C_337] : k2_xboole_0(k1_enumset1(A_335,B_336,C_337),k2_tarski(A_335,B_336)) = k2_xboole_0(k1_enumset1(A_335,B_336,C_337),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_10,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_enumset1(A_10,B_11,C_12),k2_tarski(D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16923,plain,(
    ! [A_446,B_447,C_448] : k3_enumset1(A_446,B_447,C_448,A_446,B_447) = k2_xboole_0(k1_enumset1(A_446,B_447,C_448),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9368,c_10])).

tff(c_6902,plain,(
    ! [D_257,F_260,C_255,B_256,E_258,A_259] : k2_xboole_0(k1_tarski(A_259),k3_enumset1(B_256,C_255,D_257,E_258,F_260)) = k4_enumset1(A_259,B_256,C_255,D_257,E_258,F_260) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),B_38) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7115,plain,(
    ! [E_266,C_263,F_264,B_262,D_267,A_265] : k4_enumset1(A_265,B_262,C_263,D_267,E_266,F_264) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6902,c_22])).

tff(c_7117,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k3_enumset1(A_26,B_27,C_28,D_29,E_30) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_7115])).

tff(c_16986,plain,(
    ! [A_446,B_447,C_448] : k2_xboole_0(k1_enumset1(A_446,B_447,C_448),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16923,c_7117])).

tff(c_25058,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25031,c_16986])).

tff(c_25125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6744,c_25058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:11:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.73/5.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/5.72  
% 13.81/5.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/5.72  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.81/5.72  
% 13.81/5.72  %Foreground sorts:
% 13.81/5.72  
% 13.81/5.72  
% 13.81/5.72  %Background operators:
% 13.81/5.72  
% 13.81/5.72  
% 13.81/5.72  %Foreground operators:
% 13.81/5.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.81/5.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.81/5.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.81/5.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.81/5.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.81/5.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.81/5.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.81/5.72  tff('#skF_2', type, '#skF_2': $i).
% 13.81/5.72  tff('#skF_3', type, '#skF_3': $i).
% 13.81/5.72  tff('#skF_1', type, '#skF_1': $i).
% 13.81/5.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.81/5.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.81/5.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.81/5.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.81/5.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.81/5.72  
% 13.81/5.74  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 13.81/5.74  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 13.81/5.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.81/5.74  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 13.81/5.74  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 13.81/5.74  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 13.81/5.74  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 13.81/5.74  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 13.81/5.74  tff(f_54, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 13.81/5.74  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.81/5.74  tff(f_50, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 13.81/5.74  tff(c_18, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.81/5.74  tff(c_1410, plain, (![F_124, E_122, A_123, D_121, B_120, C_119]: (k2_xboole_0(k1_tarski(A_123), k3_enumset1(B_120, C_119, D_121, E_122, F_124))=k4_enumset1(A_123, B_120, C_119, D_121, E_122, F_124))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.81/5.74  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.81/5.74  tff(c_1450, plain, (![E_138, B_137, D_141, C_136, F_139, A_140]: (k4_xboole_0(k1_tarski(A_140), k4_enumset1(A_140, B_137, C_136, D_141, E_138, F_139))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1410, c_8])).
% 13.81/5.74  tff(c_1547, plain, (![B_144, A_145, D_143, E_147, C_146]: (k4_xboole_0(k1_tarski(A_145), k3_enumset1(A_145, B_144, C_146, D_143, E_147))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1450])).
% 13.81/5.74  tff(c_12, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.81/5.74  tff(c_192, plain, (![A_61, C_62, B_63]: (k2_xboole_0(k4_xboole_0(A_61, C_62), k4_xboole_0(B_63, C_62))=k4_xboole_0(k2_xboole_0(A_61, B_63), C_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.81/5.74  tff(c_233, plain, (![A_64, C_65, B_66]: (k4_xboole_0(k4_xboole_0(A_64, C_65), k4_xboole_0(k2_xboole_0(A_64, B_66), C_65))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_192, c_8])).
% 13.81/5.74  tff(c_276, plain, (![A_15, C_65, B_16]: (k4_xboole_0(k4_xboole_0(k1_tarski(A_15), C_65), k4_xboole_0(k2_tarski(A_15, B_16), C_65))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_233])).
% 13.81/5.74  tff(c_1552, plain, (![B_16, B_144, A_145, D_143, E_147, C_146]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_tarski(A_145, B_16), k3_enumset1(A_145, B_144, C_146, D_143, E_147)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1547, c_276])).
% 13.81/5.74  tff(c_854, plain, (![B_87, E_88, C_91, A_89, D_90]: (k2_xboole_0(k1_enumset1(A_89, B_87, C_91), k2_tarski(D_90, E_88))=k3_enumset1(A_89, B_87, C_91, D_90, E_88))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.81/5.74  tff(c_875, plain, (![B_87, E_88, C_91, A_89, D_90]: (k4_xboole_0(k1_enumset1(A_89, B_87, C_91), k3_enumset1(A_89, B_87, C_91, D_90, E_88))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_854, c_8])).
% 13.81/5.74  tff(c_14, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.81/5.74  tff(c_3631, plain, (![A_193, B_194, C_195, C_196]: (k4_xboole_0(k4_xboole_0(k2_tarski(A_193, B_194), C_195), k4_xboole_0(k1_enumset1(A_193, B_194, C_196), C_195))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_233])).
% 13.81/5.74  tff(c_4724, plain, (![D_216, B_217, C_218, A_219, E_220]: (k4_xboole_0(k4_xboole_0(k2_tarski(A_219, B_217), k3_enumset1(A_219, B_217, C_218, D_216, E_220)), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_875, c_3631])).
% 13.81/5.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | k4_xboole_0(B_2, A_1)!=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.81/5.74  tff(c_4747, plain, (![D_216, B_217, C_218, A_219, E_220]: (k4_xboole_0(k2_tarski(A_219, B_217), k3_enumset1(A_219, B_217, C_218, D_216, E_220))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_tarski(A_219, B_217), k3_enumset1(A_219, B_217, C_218, D_216, E_220)))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4724, c_2])).
% 13.81/5.74  tff(c_4760, plain, (![D_216, B_217, C_218, A_219, E_220]: (k4_xboole_0(k2_tarski(A_219, B_217), k3_enumset1(A_219, B_217, C_218, D_216, E_220))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_4747])).
% 13.81/5.74  tff(c_3650, plain, (![B_87, E_88, C_91, A_89, D_90]: (k4_xboole_0(k4_xboole_0(k2_tarski(A_89, B_87), k3_enumset1(A_89, B_87, C_91, D_90, E_88)), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_875, c_3631])).
% 13.81/5.74  tff(c_4876, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4760, c_3650])).
% 13.81/5.74  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.81/5.74  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.81/5.74  tff(c_30, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(A_41, B_42))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.81/5.74  tff(c_37, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_30])).
% 13.81/5.74  tff(c_219, plain, (![B_63]: (k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), B_63), k1_xboole_0)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_63, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_192])).
% 13.81/5.74  tff(c_299, plain, (![B_67]: (k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), B_67), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_219])).
% 13.81/5.74  tff(c_337, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_299])).
% 13.81/5.74  tff(c_4921, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4876, c_337])).
% 13.81/5.74  tff(c_44, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.81/5.74  tff(c_60, plain, (k2_xboole_0(k1_xboole_0, k2_tarski('#skF_1', '#skF_2'))=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37, c_44])).
% 13.81/5.74  tff(c_982, plain, (![A_95]: (k4_xboole_0(k2_xboole_0(A_95, k2_tarski('#skF_1', '#skF_2')), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_95, k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_37, c_192])).
% 13.81/5.74  tff(c_1036, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k4_xboole_0(k1_xboole_0, k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_982])).
% 13.81/5.74  tff(c_1045, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_1036])).
% 13.81/5.74  tff(c_1114, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, k1_xboole_0))!=k2_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1045, c_2])).
% 13.81/5.74  tff(c_1125, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k2_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_3'), k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1114])).
% 13.81/5.74  tff(c_1127, plain, (k2_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_3'), k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1125])).
% 13.81/5.74  tff(c_4975, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4921, c_1127])).
% 13.81/5.74  tff(c_289, plain, (![A_64, B_66, B_9]: (k4_xboole_0(k4_xboole_0(A_64, k2_xboole_0(k2_xboole_0(A_64, B_66), B_9)), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_233])).
% 13.81/5.74  tff(c_358, plain, (![C_68]: (k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_68), k4_xboole_0(k1_xboole_0, C_68))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_233])).
% 13.81/5.74  tff(c_3371, plain, (![C_190]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, C_190), k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_190))=k2_xboole_0(k4_xboole_0(k1_xboole_0, C_190), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_358, c_4])).
% 13.81/5.74  tff(c_6, plain, (![A_5, C_7, B_6]: (k2_xboole_0(k4_xboole_0(A_5, C_7), k4_xboole_0(B_6, C_7))=k4_xboole_0(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.81/5.74  tff(c_3398, plain, (![C_190]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, k2_tarski('#skF_1', '#skF_2')), C_190)=k2_xboole_0(k4_xboole_0(k1_xboole_0, C_190), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3371, c_6])).
% 13.81/5.74  tff(c_3475, plain, (![C_191]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, k1_xboole_0), C_191)=k2_xboole_0(k4_xboole_0(k1_xboole_0, C_191), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3398])).
% 13.81/5.74  tff(c_3550, plain, (![B_9]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, k2_xboole_0(k2_xboole_0(k1_xboole_0, k1_xboole_0), B_9)), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3475, c_8])).
% 13.81/5.74  tff(c_351, plain, (![A_5]: (k2_xboole_0(k4_xboole_0(A_5, k1_xboole_0), k2_xboole_0(k1_xboole_0, '#skF_3'))=k4_xboole_0(k2_xboole_0(A_5, k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_337, c_6])).
% 13.81/5.74  tff(c_6642, plain, (![A_247]: (k4_xboole_0(k2_xboole_0(A_247, k1_xboole_0), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_247, k1_xboole_0), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4921, c_351])).
% 13.81/5.74  tff(c_6708, plain, (![B_9]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0, k2_xboole_0(k2_xboole_0(k1_xboole_0, k1_xboole_0), B_9)), k1_xboole_0), k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3550, c_6642])).
% 13.81/5.74  tff(c_6741, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4876, c_289, c_6708])).
% 13.81/5.74  tff(c_6743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4975, c_6741])).
% 13.81/5.74  tff(c_6744, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1125])).
% 13.81/5.74  tff(c_135, plain, (![A_59, B_60]: (k2_xboole_0(k2_xboole_0(A_59, B_60), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_59, B_60), A_59))), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 13.81/5.74  tff(c_171, plain, (![A_15, B_16]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16)), k1_xboole_0)=k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_135])).
% 13.81/5.74  tff(c_7584, plain, (![A_296, B_297]: (k2_xboole_0(k2_tarski(A_296, B_297), k1_tarski(A_296))=k2_xboole_0(k2_tarski(A_296, B_297), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_171])).
% 13.81/5.74  tff(c_7634, plain, (![A_298, B_299]: (k2_xboole_0(k2_tarski(A_298, B_299), k1_xboole_0)=k1_enumset1(A_298, B_299, A_298))), inference(superposition, [status(thm), theory('equality')], [c_7584, c_14])).
% 13.81/5.74  tff(c_232, plain, (![B_63]: (k4_xboole_0(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), B_63), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_63))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_219])).
% 13.81/5.74  tff(c_7669, plain, (k4_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7634, c_232])).
% 13.81/5.74  tff(c_7691, plain, (k4_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6744, c_7669])).
% 13.81/5.74  tff(c_7714, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_1')=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_enumset1('#skF_1', '#skF_2', '#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7691, c_2])).
% 13.81/5.74  tff(c_22651, plain, (k4_xboole_0(k1_xboole_0, k1_enumset1('#skF_1', '#skF_2', '#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7714])).
% 13.81/5.74  tff(c_398, plain, (![B_9]: (k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_xboole_0(k1_xboole_0, B_9)), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_358])).
% 13.81/5.74  tff(c_6758, plain, (k4_xboole_0(k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6744, c_398])).
% 13.81/5.74  tff(c_6778, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_337, c_37, c_6758])).
% 13.81/5.74  tff(c_8145, plain, (![A_313, B_314, B_315]: (k4_xboole_0(k2_xboole_0(A_313, B_314), k2_xboole_0(A_313, B_315))=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_314, k2_xboole_0(A_313, B_315))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_192])).
% 13.81/5.74  tff(c_8288, plain, (![A_17, B_18, B_314, C_19]: (k4_xboole_0(k2_xboole_0(k2_tarski(A_17, B_18), B_314), k1_enumset1(A_17, B_18, C_19))=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_314, k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(C_19)))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8145])).
% 13.81/5.74  tff(c_24580, plain, (![A_560, B_561, B_562, C_563]: (k4_xboole_0(k2_xboole_0(k2_tarski(A_560, B_561), B_562), k1_enumset1(A_560, B_561, C_563))=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_562, k1_enumset1(A_560, B_561, C_563))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8288])).
% 13.81/5.74  tff(c_24903, plain, (![C_572]: (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', k1_enumset1('#skF_1', '#skF_2', C_572)))=k4_xboole_0(k1_xboole_0, k1_enumset1('#skF_1', '#skF_2', C_572)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_24580])).
% 13.81/5.74  tff(c_7705, plain, (![B_6]: (k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), B_6), k1_xboole_0)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_6, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_7691, c_6])).
% 13.81/5.74  tff(c_7724, plain, (![B_6]: (k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), B_6), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7705])).
% 13.81/5.74  tff(c_10618, plain, (![B_358]: (k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), B_358), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_358))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7705])).
% 13.81/5.74  tff(c_10679, plain, (![B_4]: (k4_xboole_0(k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_1'), B_4), k1_xboole_0)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_4, k1_enumset1('#skF_1', '#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_10618])).
% 13.81/5.74  tff(c_10689, plain, (![B_4]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_4, k1_enumset1('#skF_1', '#skF_2', '#skF_1')))=k2_xboole_0(k1_xboole_0, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_7724, c_10679])).
% 13.81/5.74  tff(c_24959, plain, (k4_xboole_0(k1_xboole_0, k1_enumset1('#skF_1', '#skF_2', '#skF_1'))=k2_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24903, c_10689])).
% 13.81/5.74  tff(c_25028, plain, (k4_xboole_0(k1_xboole_0, k1_enumset1('#skF_1', '#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6778, c_24959])).
% 13.81/5.74  tff(c_25030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22651, c_25028])).
% 13.81/5.74  tff(c_25031, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7714])).
% 13.81/5.74  tff(c_168, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(C_19)), k1_xboole_0)=k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k2_tarski(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_135])).
% 13.81/5.74  tff(c_9368, plain, (![A_335, B_336, C_337]: (k2_xboole_0(k1_enumset1(A_335, B_336, C_337), k2_tarski(A_335, B_336))=k2_xboole_0(k1_enumset1(A_335, B_336, C_337), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_168])).
% 13.81/5.74  tff(c_10, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_enumset1(A_10, B_11, C_12), k2_tarski(D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.81/5.74  tff(c_16923, plain, (![A_446, B_447, C_448]: (k3_enumset1(A_446, B_447, C_448, A_446, B_447)=k2_xboole_0(k1_enumset1(A_446, B_447, C_448), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9368, c_10])).
% 13.81/5.74  tff(c_6902, plain, (![D_257, F_260, C_255, B_256, E_258, A_259]: (k2_xboole_0(k1_tarski(A_259), k3_enumset1(B_256, C_255, D_257, E_258, F_260))=k4_enumset1(A_259, B_256, C_255, D_257, E_258, F_260))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.81/5.74  tff(c_22, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.81/5.74  tff(c_7115, plain, (![E_266, C_263, F_264, B_262, D_267, A_265]: (k4_enumset1(A_265, B_262, C_263, D_267, E_266, F_264)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6902, c_22])).
% 13.81/5.74  tff(c_7117, plain, (![B_27, D_29, A_26, E_30, C_28]: (k3_enumset1(A_26, B_27, C_28, D_29, E_30)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_7115])).
% 13.81/5.74  tff(c_16986, plain, (![A_446, B_447, C_448]: (k2_xboole_0(k1_enumset1(A_446, B_447, C_448), k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16923, c_7117])).
% 13.81/5.74  tff(c_25058, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25031, c_16986])).
% 13.81/5.74  tff(c_25125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6744, c_25058])).
% 13.81/5.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/5.74  
% 13.81/5.74  Inference rules
% 13.81/5.74  ----------------------
% 13.81/5.74  #Ref     : 1
% 13.81/5.74  #Sup     : 7049
% 13.81/5.74  #Fact    : 0
% 13.81/5.74  #Define  : 0
% 13.81/5.74  #Split   : 4
% 13.81/5.74  #Chain   : 0
% 13.81/5.74  #Close   : 0
% 13.81/5.74  
% 13.81/5.74  Ordering : KBO
% 13.81/5.74  
% 13.81/5.74  Simplification rules
% 13.81/5.74  ----------------------
% 13.81/5.74  #Subsume      : 27
% 13.81/5.74  #Demod        : 8323
% 13.81/5.74  #Tautology    : 4364
% 13.81/5.74  #SimpNegUnit  : 6
% 13.81/5.74  #BackRed      : 33
% 13.81/5.74  
% 13.81/5.74  #Partial instantiations: 0
% 13.81/5.74  #Strategies tried      : 1
% 13.81/5.74  
% 13.81/5.74  Timing (in seconds)
% 13.81/5.74  ----------------------
% 13.81/5.74  Preprocessing        : 0.31
% 13.81/5.74  Parsing              : 0.17
% 13.81/5.74  CNF conversion       : 0.02
% 13.81/5.74  Main loop            : 4.60
% 13.81/5.74  Inferencing          : 0.80
% 13.81/5.74  Reduction            : 2.95
% 13.81/5.74  Demodulation         : 2.66
% 13.81/5.74  BG Simplification    : 0.10
% 13.81/5.74  Subsumption          : 0.56
% 13.81/5.74  Abstraction          : 0.16
% 13.81/5.74  MUC search           : 0.00
% 13.81/5.74  Cooper               : 0.00
% 13.81/5.74  Total                : 4.95
% 13.81/5.74  Index Insertion      : 0.00
% 13.81/5.74  Index Deletion       : 0.00
% 13.81/5.74  Index Matching       : 0.00
% 13.81/5.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
