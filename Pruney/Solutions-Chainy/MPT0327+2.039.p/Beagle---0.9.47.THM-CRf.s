%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  123 (1772 expanded)
%              Number of leaves         :   33 ( 622 expanded)
%              Depth                    :   19
%              Number of atoms          :  121 (2221 expanded)
%              Number of equality atoms :   87 (1553 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_276,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k1_tarski(A_61),B_62) = k1_xboole_0
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_276,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_680,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_698,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_680])).

tff(c_32,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_945,plain,(
    ! [A_107,B_108,C_109] : k5_xboole_0(k5_xboole_0(A_107,B_108),C_109) = k5_xboole_0(A_107,k5_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_986,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k5_xboole_0(B_26,k3_xboole_0(A_25,B_26))) = k2_xboole_0(A_25,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_945])).

tff(c_1796,plain,(
    ! [A_133,B_134] : k5_xboole_0(A_133,k4_xboole_0(B_134,A_133)) = k2_xboole_0(A_133,B_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_986])).

tff(c_1822,plain,(
    ! [B_62,A_61] :
      ( k2_xboole_0(B_62,k1_tarski(A_61)) = k5_xboole_0(B_62,k1_xboole_0)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_1796])).

tff(c_1856,plain,(
    ! [B_62,A_61] :
      ( k2_xboole_0(B_62,k1_tarski(A_61)) = B_62
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1822])).

tff(c_24,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_232,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_135,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_695,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_680])).

tff(c_706,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_695])).

tff(c_3974,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k5_xboole_0(B_180,k5_xboole_0(A_179,B_180))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_706])).

tff(c_20,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_166,plain,(
    ! [A_55] : k3_xboole_0(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_855,plain,(
    ! [A_102,B_103] : k5_xboole_0(k5_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_894,plain,(
    ! [A_21] : k5_xboole_0(A_21,k3_xboole_0(A_21,k1_xboole_0)) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_855])).

tff(c_902,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_166,c_894])).

tff(c_467,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_488,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_467])).

tff(c_904,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_488])).

tff(c_885,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_855])).

tff(c_901,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_885])).

tff(c_1023,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_901])).

tff(c_996,plain,(
    ! [B_4,C_109] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_109)) = k5_xboole_0(k1_xboole_0,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_945])).

tff(c_3880,plain,(
    ! [B_4,C_109] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_996])).

tff(c_3982,plain,(
    ! [B_180,A_179] : k5_xboole_0(B_180,k5_xboole_0(A_179,B_180)) = k5_xboole_0(A_179,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3974,c_3880])).

tff(c_4074,plain,(
    ! [B_180,A_179] : k5_xboole_0(B_180,k5_xboole_0(A_179,B_180)) = A_179 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3982])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1224,plain,(
    ! [A_120,B_121] : k3_xboole_0(k4_xboole_0(A_120,B_121),A_120) = k4_xboole_0(A_120,B_121) ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_1233,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k4_xboole_0(A_120,k4_xboole_0(A_120,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_698])).

tff(c_1299,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1233])).

tff(c_242,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_232])).

tff(c_1845,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k5_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_1796])).

tff(c_1861,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1845])).

tff(c_145,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k4_xboole_0(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_4193,plain,(
    ! [B_183,A_184] : k5_xboole_0(k5_xboole_0(B_183,A_184),k3_xboole_0(A_184,B_183)) = k2_xboole_0(B_183,A_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_855])).

tff(c_4278,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,k4_xboole_0(A_15,B_16)),k4_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_4193])).

tff(c_4339,plain,(
    ! [A_15,B_16] : k5_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1861,c_4278])).

tff(c_13541,plain,(
    ! [A_293,B_294,C_295] : k5_xboole_0(k5_xboole_0(A_293,B_294),k5_xboole_0(k3_xboole_0(A_293,B_294),C_295)) = k5_xboole_0(k2_xboole_0(A_293,B_294),C_295) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_945])).

tff(c_13722,plain,(
    ! [A_15,B_16] : k5_xboole_0(k2_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = k5_xboole_0(k5_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_4339,c_13541])).

tff(c_14223,plain,(
    ! [A_300,B_301] : k5_xboole_0(k2_xboole_0(A_300,B_301),k4_xboole_0(A_300,B_301)) = B_301 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_30,c_13722])).

tff(c_4095,plain,(
    ! [B_181,A_182] : k5_xboole_0(B_181,k5_xboole_0(A_182,B_181)) = A_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3982])).

tff(c_4140,plain,(
    ! [B_4,C_109] : k5_xboole_0(k5_xboole_0(B_4,C_109),C_109) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_4095])).

tff(c_1021,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_986])).

tff(c_1317,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k3_xboole_0(A_122,B_123),k3_xboole_0(C_124,B_123)) = k3_xboole_0(k5_xboole_0(A_122,C_124),B_123) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1366,plain,(
    ! [B_4,C_124] : k5_xboole_0(B_4,k3_xboole_0(C_124,B_4)) = k3_xboole_0(k5_xboole_0(B_4,C_124),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1317])).

tff(c_1394,plain,(
    ! [B_4,C_124] : k3_xboole_0(B_4,k5_xboole_0(B_4,C_124)) = k4_xboole_0(B_4,C_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_2,c_1366])).

tff(c_4248,plain,(
    ! [B_4,C_124] : k5_xboole_0(k5_xboole_0(k5_xboole_0(B_4,C_124),B_4),k4_xboole_0(B_4,C_124)) = k2_xboole_0(k5_xboole_0(B_4,C_124),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_4193])).

tff(c_6514,plain,(
    ! [B_217,C_218] : k2_xboole_0(k5_xboole_0(B_217,C_218),B_217) = k2_xboole_0(B_217,C_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_698,c_1299,c_30,c_30,c_30,c_4248])).

tff(c_347,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_523,plain,(
    ! [A_81,B_82] : k4_xboole_0(k3_xboole_0(A_81,B_82),A_81) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_242])).

tff(c_559,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_523])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1334,plain,(
    ! [A_122,B_123] : k3_xboole_0(k5_xboole_0(A_122,k3_xboole_0(A_122,B_123)),B_123) = k4_xboole_0(k3_xboole_0(A_122,B_123),B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_14])).

tff(c_1396,plain,(
    ! [B_125,A_126] : k3_xboole_0(B_125,k4_xboole_0(A_126,B_125)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_2,c_14,c_1334])).

tff(c_1416,plain,(
    ! [B_125,A_126] : k4_xboole_0(B_125,k4_xboole_0(A_126,B_125)) = k5_xboole_0(B_125,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_14])).

tff(c_1464,plain,(
    ! [B_125,A_126] : k4_xboole_0(B_125,k4_xboole_0(A_126,B_125)) = B_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1416])).

tff(c_2740,plain,(
    ! [B_155,C_156] : k3_xboole_0(B_155,k5_xboole_0(B_155,C_156)) = k4_xboole_0(B_155,C_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_2,c_1366])).

tff(c_2803,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k3_xboole_0(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_2740])).

tff(c_2850,plain,(
    ! [A_157,B_158] : k3_xboole_0(A_157,k2_xboole_0(A_157,B_158)) = A_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1464,c_2803])).

tff(c_440,plain,(
    ! [A_75,B_76] : r1_tarski(k3_xboole_0(A_75,B_76),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_22])).

tff(c_458,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_440])).

tff(c_2893,plain,(
    ! [A_157,B_158] : r1_tarski(A_157,k2_xboole_0(A_157,B_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2850,c_458])).

tff(c_6621,plain,(
    ! [B_219,C_220] : r1_tarski(k5_xboole_0(B_219,C_220),k2_xboole_0(B_219,C_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6514,c_2893])).

tff(c_6662,plain,(
    ! [B_4,C_109] : r1_tarski(B_4,k2_xboole_0(k5_xboole_0(B_4,C_109),C_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4140,c_6621])).

tff(c_14251,plain,(
    ! [A_300,B_301] : r1_tarski(k2_xboole_0(A_300,B_301),k2_xboole_0(B_301,k4_xboole_0(A_300,B_301))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14223,c_6662])).

tff(c_14409,plain,(
    ! [A_300,B_301] : r1_tarski(k2_xboole_0(A_300,B_301),k2_xboole_0(B_301,A_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14251])).

tff(c_14442,plain,(
    ! [A_302,B_303] : r1_tarski(k2_xboole_0(A_302,B_303),k2_xboole_0(B_303,A_302)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14251])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14447,plain,(
    ! [B_303,A_302] :
      ( k2_xboole_0(B_303,A_302) = k2_xboole_0(A_302,B_303)
      | ~ r1_tarski(k2_xboole_0(B_303,A_302),k2_xboole_0(A_302,B_303)) ) ),
    inference(resolution,[status(thm)],[c_14442,c_4])).

tff(c_14547,plain,(
    ! [B_303,A_302] : k2_xboole_0(B_303,A_302) = k2_xboole_0(A_302,B_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14409,c_14447])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14571,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14547,c_48])).

tff(c_14573,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14547,c_24,c_14571])).

tff(c_14923,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1856,c_14573])).

tff(c_14927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.03/3.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/3.34  
% 8.03/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/3.34  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.03/3.34  
% 8.03/3.34  %Foreground sorts:
% 8.03/3.34  
% 8.03/3.34  
% 8.03/3.34  %Background operators:
% 8.03/3.34  
% 8.03/3.34  
% 8.03/3.34  %Foreground operators:
% 8.03/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.03/3.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.03/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.03/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/3.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.03/3.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.03/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.03/3.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.03/3.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.03/3.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.03/3.34  tff('#skF_2', type, '#skF_2': $i).
% 8.03/3.34  tff('#skF_1', type, '#skF_1': $i).
% 8.03/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/3.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.03/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/3.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.03/3.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.03/3.34  
% 8.03/3.36  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 8.03/3.36  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.03/3.36  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.03/3.36  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.03/3.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.03/3.36  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.03/3.36  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.03/3.36  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.03/3.36  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.03/3.36  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.03/3.36  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.03/3.36  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.03/3.36  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.03/3.36  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.03/3.36  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.03/3.36  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/3.36  tff(c_28, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.03/3.36  tff(c_276, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.03/3.36  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.03/3.36  tff(c_283, plain, (![A_61, B_62]: (k4_xboole_0(k1_tarski(A_61), B_62)=k1_xboole_0 | ~r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_276, c_12])).
% 8.03/3.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.03/3.36  tff(c_680, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/3.36  tff(c_698, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_680])).
% 8.03/3.36  tff(c_32, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/3.36  tff(c_945, plain, (![A_107, B_108, C_109]: (k5_xboole_0(k5_xboole_0(A_107, B_108), C_109)=k5_xboole_0(A_107, k5_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.03/3.36  tff(c_986, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k5_xboole_0(B_26, k3_xboole_0(A_25, B_26)))=k2_xboole_0(A_25, B_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_945])).
% 8.03/3.36  tff(c_1796, plain, (![A_133, B_134]: (k5_xboole_0(A_133, k4_xboole_0(B_134, A_133))=k2_xboole_0(A_133, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_986])).
% 8.03/3.36  tff(c_1822, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k1_tarski(A_61))=k5_xboole_0(B_62, k1_xboole_0) | ~r2_hidden(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_283, c_1796])).
% 8.03/3.36  tff(c_1856, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k1_tarski(A_61))=B_62 | ~r2_hidden(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1822])).
% 8.03/3.36  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.03/3.36  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/3.36  tff(c_232, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.03/3.36  tff(c_243, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_232])).
% 8.03/3.36  tff(c_135, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.03/3.36  tff(c_146, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_135])).
% 8.03/3.36  tff(c_695, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_680])).
% 8.03/3.36  tff(c_706, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_695])).
% 8.03/3.36  tff(c_3974, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k5_xboole_0(B_180, k5_xboole_0(A_179, B_180)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_945, c_706])).
% 8.03/3.36  tff(c_20, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.03/3.36  tff(c_157, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_135])).
% 8.03/3.36  tff(c_166, plain, (![A_55]: (k3_xboole_0(A_55, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 8.03/3.36  tff(c_855, plain, (![A_102, B_103]: (k5_xboole_0(k5_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/3.36  tff(c_894, plain, (![A_21]: (k5_xboole_0(A_21, k3_xboole_0(A_21, k1_xboole_0))=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_855])).
% 8.03/3.36  tff(c_902, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_166, c_894])).
% 8.03/3.36  tff(c_467, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.03/3.36  tff(c_488, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_243, c_467])).
% 8.03/3.36  tff(c_904, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_902, c_488])).
% 8.03/3.36  tff(c_885, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_855])).
% 8.03/3.36  tff(c_901, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_885])).
% 8.03/3.36  tff(c_1023, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_904, c_901])).
% 8.03/3.36  tff(c_996, plain, (![B_4, C_109]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_109))=k5_xboole_0(k1_xboole_0, C_109))), inference(superposition, [status(thm), theory('equality')], [c_706, c_945])).
% 8.03/3.36  tff(c_3880, plain, (![B_4, C_109]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_996])).
% 8.03/3.36  tff(c_3982, plain, (![B_180, A_179]: (k5_xboole_0(B_180, k5_xboole_0(A_179, B_180))=k5_xboole_0(A_179, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3974, c_3880])).
% 8.03/3.36  tff(c_4074, plain, (![B_180, A_179]: (k5_xboole_0(B_180, k5_xboole_0(A_179, B_180))=A_179)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3982])).
% 8.03/3.36  tff(c_30, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.03/3.36  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.03/3.36  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.03/3.36  tff(c_1224, plain, (![A_120, B_121]: (k3_xboole_0(k4_xboole_0(A_120, B_121), A_120)=k4_xboole_0(A_120, B_121))), inference(resolution, [status(thm)], [c_22, c_135])).
% 8.03/3.36  tff(c_1233, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k4_xboole_0(A_120, k4_xboole_0(A_120, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_698])).
% 8.03/3.36  tff(c_1299, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1233])).
% 8.03/3.36  tff(c_242, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_232])).
% 8.03/3.36  tff(c_1845, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k5_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_242, c_1796])).
% 8.03/3.36  tff(c_1861, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(A_15, B_16))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1845])).
% 8.03/3.36  tff(c_145, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k4_xboole_0(A_15, B_16))), inference(resolution, [status(thm)], [c_22, c_135])).
% 8.03/3.36  tff(c_4193, plain, (![B_183, A_184]: (k5_xboole_0(k5_xboole_0(B_183, A_184), k3_xboole_0(A_184, B_183))=k2_xboole_0(B_183, A_184))), inference(superposition, [status(thm), theory('equality')], [c_2, c_855])).
% 8.03/3.36  tff(c_4278, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, k4_xboole_0(A_15, B_16)), k4_xboole_0(A_15, B_16))=k2_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_4193])).
% 8.03/3.36  tff(c_4339, plain, (![A_15, B_16]: (k5_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1861, c_4278])).
% 8.03/3.36  tff(c_13541, plain, (![A_293, B_294, C_295]: (k5_xboole_0(k5_xboole_0(A_293, B_294), k5_xboole_0(k3_xboole_0(A_293, B_294), C_295))=k5_xboole_0(k2_xboole_0(A_293, B_294), C_295))), inference(superposition, [status(thm), theory('equality')], [c_32, c_945])).
% 8.03/3.36  tff(c_13722, plain, (![A_15, B_16]: (k5_xboole_0(k2_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=k5_xboole_0(k5_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_4339, c_13541])).
% 8.03/3.36  tff(c_14223, plain, (![A_300, B_301]: (k5_xboole_0(k2_xboole_0(A_300, B_301), k4_xboole_0(A_300, B_301))=B_301)), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_30, c_13722])).
% 8.03/3.36  tff(c_4095, plain, (![B_181, A_182]: (k5_xboole_0(B_181, k5_xboole_0(A_182, B_181))=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3982])).
% 8.03/3.36  tff(c_4140, plain, (![B_4, C_109]: (k5_xboole_0(k5_xboole_0(B_4, C_109), C_109)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_3880, c_4095])).
% 8.03/3.36  tff(c_1021, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_986])).
% 8.03/3.36  tff(c_1317, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k3_xboole_0(A_122, B_123), k3_xboole_0(C_124, B_123))=k3_xboole_0(k5_xboole_0(A_122, C_124), B_123))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.03/3.36  tff(c_1366, plain, (![B_4, C_124]: (k5_xboole_0(B_4, k3_xboole_0(C_124, B_4))=k3_xboole_0(k5_xboole_0(B_4, C_124), B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1317])).
% 8.03/3.36  tff(c_1394, plain, (![B_4, C_124]: (k3_xboole_0(B_4, k5_xboole_0(B_4, C_124))=k4_xboole_0(B_4, C_124))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_2, c_1366])).
% 8.03/3.36  tff(c_4248, plain, (![B_4, C_124]: (k5_xboole_0(k5_xboole_0(k5_xboole_0(B_4, C_124), B_4), k4_xboole_0(B_4, C_124))=k2_xboole_0(k5_xboole_0(B_4, C_124), B_4))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_4193])).
% 8.03/3.36  tff(c_6514, plain, (![B_217, C_218]: (k2_xboole_0(k5_xboole_0(B_217, C_218), B_217)=k2_xboole_0(B_217, C_218))), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_698, c_1299, c_30, c_30, c_30, c_4248])).
% 8.03/3.36  tff(c_347, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.03/3.36  tff(c_523, plain, (![A_81, B_82]: (k4_xboole_0(k3_xboole_0(A_81, B_82), A_81)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_242])).
% 8.03/3.36  tff(c_559, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_523])).
% 8.03/3.36  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/3.36  tff(c_1334, plain, (![A_122, B_123]: (k3_xboole_0(k5_xboole_0(A_122, k3_xboole_0(A_122, B_123)), B_123)=k4_xboole_0(k3_xboole_0(A_122, B_123), B_123))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_14])).
% 8.03/3.36  tff(c_1396, plain, (![B_125, A_126]: (k3_xboole_0(B_125, k4_xboole_0(A_126, B_125))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_559, c_2, c_14, c_1334])).
% 8.03/3.36  tff(c_1416, plain, (![B_125, A_126]: (k4_xboole_0(B_125, k4_xboole_0(A_126, B_125))=k5_xboole_0(B_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_14])).
% 8.03/3.36  tff(c_1464, plain, (![B_125, A_126]: (k4_xboole_0(B_125, k4_xboole_0(A_126, B_125))=B_125)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1416])).
% 8.03/3.36  tff(c_2740, plain, (![B_155, C_156]: (k3_xboole_0(B_155, k5_xboole_0(B_155, C_156))=k4_xboole_0(B_155, C_156))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_2, c_1366])).
% 8.03/3.36  tff(c_2803, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k3_xboole_0(A_25, k2_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_1021, c_2740])).
% 8.03/3.36  tff(c_2850, plain, (![A_157, B_158]: (k3_xboole_0(A_157, k2_xboole_0(A_157, B_158))=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_1464, c_2803])).
% 8.03/3.36  tff(c_440, plain, (![A_75, B_76]: (r1_tarski(k3_xboole_0(A_75, B_76), A_75))), inference(superposition, [status(thm), theory('equality')], [c_347, c_22])).
% 8.03/3.36  tff(c_458, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_440])).
% 8.03/3.36  tff(c_2893, plain, (![A_157, B_158]: (r1_tarski(A_157, k2_xboole_0(A_157, B_158)))), inference(superposition, [status(thm), theory('equality')], [c_2850, c_458])).
% 8.03/3.36  tff(c_6621, plain, (![B_219, C_220]: (r1_tarski(k5_xboole_0(B_219, C_220), k2_xboole_0(B_219, C_220)))), inference(superposition, [status(thm), theory('equality')], [c_6514, c_2893])).
% 8.03/3.36  tff(c_6662, plain, (![B_4, C_109]: (r1_tarski(B_4, k2_xboole_0(k5_xboole_0(B_4, C_109), C_109)))), inference(superposition, [status(thm), theory('equality')], [c_4140, c_6621])).
% 8.03/3.36  tff(c_14251, plain, (![A_300, B_301]: (r1_tarski(k2_xboole_0(A_300, B_301), k2_xboole_0(B_301, k4_xboole_0(A_300, B_301))))), inference(superposition, [status(thm), theory('equality')], [c_14223, c_6662])).
% 8.03/3.36  tff(c_14409, plain, (![A_300, B_301]: (r1_tarski(k2_xboole_0(A_300, B_301), k2_xboole_0(B_301, A_300)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14251])).
% 8.03/3.36  tff(c_14442, plain, (![A_302, B_303]: (r1_tarski(k2_xboole_0(A_302, B_303), k2_xboole_0(B_303, A_302)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14251])).
% 8.03/3.36  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/3.36  tff(c_14447, plain, (![B_303, A_302]: (k2_xboole_0(B_303, A_302)=k2_xboole_0(A_302, B_303) | ~r1_tarski(k2_xboole_0(B_303, A_302), k2_xboole_0(A_302, B_303)))), inference(resolution, [status(thm)], [c_14442, c_4])).
% 8.03/3.36  tff(c_14547, plain, (![B_303, A_302]: (k2_xboole_0(B_303, A_302)=k2_xboole_0(A_302, B_303))), inference(demodulation, [status(thm), theory('equality')], [c_14409, c_14447])).
% 8.03/3.36  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.03/3.36  tff(c_14571, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14547, c_48])).
% 8.03/3.36  tff(c_14573, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14547, c_24, c_14571])).
% 8.03/3.36  tff(c_14923, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1856, c_14573])).
% 8.03/3.36  tff(c_14927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_14923])).
% 8.03/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/3.36  
% 8.03/3.36  Inference rules
% 8.03/3.36  ----------------------
% 8.03/3.36  #Ref     : 0
% 8.03/3.36  #Sup     : 3763
% 8.03/3.36  #Fact    : 0
% 8.03/3.36  #Define  : 0
% 8.03/3.37  #Split   : 1
% 8.03/3.37  #Chain   : 0
% 8.03/3.37  #Close   : 0
% 8.03/3.37  
% 8.03/3.37  Ordering : KBO
% 8.03/3.37  
% 8.03/3.37  Simplification rules
% 8.03/3.37  ----------------------
% 8.03/3.37  #Subsume      : 131
% 8.03/3.37  #Demod        : 4037
% 8.03/3.37  #Tautology    : 2337
% 8.03/3.37  #SimpNegUnit  : 0
% 8.03/3.37  #BackRed      : 6
% 8.03/3.37  
% 8.03/3.37  #Partial instantiations: 0
% 8.03/3.37  #Strategies tried      : 1
% 8.03/3.37  
% 8.03/3.37  Timing (in seconds)
% 8.03/3.37  ----------------------
% 8.03/3.37  Preprocessing        : 0.35
% 8.03/3.37  Parsing              : 0.18
% 8.03/3.37  CNF conversion       : 0.03
% 8.03/3.37  Main loop            : 2.11
% 8.03/3.37  Inferencing          : 0.51
% 8.03/3.37  Reduction            : 1.10
% 8.03/3.37  Demodulation         : 0.96
% 8.03/3.37  BG Simplification    : 0.07
% 8.03/3.37  Subsumption          : 0.33
% 8.03/3.37  Abstraction          : 0.11
% 8.03/3.37  MUC search           : 0.00
% 8.03/3.37  Cooper               : 0.00
% 8.03/3.37  Total                : 2.51
% 8.03/3.37  Index Insertion      : 0.00
% 8.03/3.37  Index Deletion       : 0.00
% 8.03/3.37  Index Matching       : 0.00
% 8.03/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
