%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 397 expanded)
%              Number of leaves         :   34 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :   95 ( 479 expanded)
%              Number of equality atoms :   69 ( 306 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_73,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_898,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_40] : r1_tarski(A_40,k1_zfmisc_1(k3_tarski(A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_139,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_zfmisc_1(k3_tarski(A_40))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_139])).

tff(c_160,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [A_40] : k3_xboole_0(A_40,k1_zfmisc_1(k3_tarski(A_40))) = A_40 ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_574,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_583,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_zfmisc_1(k3_tarski(A_40))) = k5_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_574])).

tff(c_601,plain,(
    ! [A_40] : k5_xboole_0(A_40,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_583])).

tff(c_3954,plain,(
    ! [A_179,B_180] : k5_xboole_0(A_179,k5_xboole_0(B_180,k5_xboole_0(A_179,B_180))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_601])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [B_63] : k4_xboole_0(B_63,B_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [B_64] : r1_tarski(k1_xboole_0,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_224,plain,(
    ! [B_68] : k3_xboole_0(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [B_68] : k3_xboole_0(B_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2])).

tff(c_1243,plain,(
    ! [A_113,B_114] : k5_xboole_0(k5_xboole_0(A_113,B_114),k3_xboole_0(A_113,B_114)) = k2_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1298,plain,(
    ! [A_20] : k5_xboole_0(A_20,k3_xboole_0(A_20,k1_xboole_0)) = k2_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1243])).

tff(c_1307,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_233,c_1298])).

tff(c_159,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_675,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_699,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_675])).

tff(c_1310,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_699])).

tff(c_180,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_1289,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_1243])).

tff(c_1306,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_1289])).

tff(c_1425,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_1306])).

tff(c_925,plain,(
    ! [A_40,C_103] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_898])).

tff(c_3880,plain,(
    ! [A_40,C_103] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_925])).

tff(c_3962,plain,(
    ! [B_180,A_179] : k5_xboole_0(B_180,k5_xboole_0(A_179,B_180)) = k5_xboole_0(A_179,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3954,c_3880])).

tff(c_4039,plain,(
    ! [B_180,A_179] : k5_xboole_0(B_180,k5_xboole_0(A_179,B_180)) = A_179 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3962])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] : k5_xboole_0(k5_xboole_0(A_21,B_22),C_23) = k5_xboole_0(A_21,k5_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4140,plain,(
    ! [A_183,B_184] :
      ( k3_xboole_0(k1_tarski(A_183),B_184) = k1_tarski(A_183)
      | ~ r2_hidden(A_183,B_184) ) ),
    inference(resolution,[status(thm)],[c_42,c_160])).

tff(c_30,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4193,plain,(
    ! [A_183,B_184] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_183),B_184),k1_tarski(A_183)) = k2_xboole_0(k1_tarski(A_183),B_184)
      | ~ r2_hidden(A_183,B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4140,c_30])).

tff(c_4287,plain,(
    ! [A_183,B_184] :
      ( k2_xboole_0(k1_tarski(A_183),B_184) = B_184
      | ~ r2_hidden(A_183,B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4039,c_28,c_4193])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5215,plain,(
    ! [B_198,A_199] : k5_xboole_0(k5_xboole_0(B_198,A_199),k3_xboole_0(A_199,B_198)) = k2_xboole_0(B_198,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1243])).

tff(c_5341,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k5_xboole_0(B_22,k3_xboole_0(B_22,A_21))) = k2_xboole_0(A_21,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5215])).

tff(c_5392,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5341])).

tff(c_4057,plain,(
    ! [B_181,A_182] : k5_xboole_0(B_181,k5_xboole_0(A_182,B_181)) = A_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3962])).

tff(c_4066,plain,(
    ! [B_181,A_182] : k5_xboole_0(B_181,A_182) = k5_xboole_0(A_182,B_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_4057,c_3880])).

tff(c_980,plain,(
    ! [A_106,B_107,C_108] : k4_xboole_0(k3_xboole_0(A_106,B_107),C_108) = k3_xboole_0(A_106,k4_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_393,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_469,plain,(
    ! [A_78,B_79] : r1_tarski(k3_xboole_0(A_78,B_79),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_18])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_501,plain,(
    ! [A_78,B_79] : k4_xboole_0(k3_xboole_0(A_78,B_79),A_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_469,c_12])).

tff(c_991,plain,(
    ! [C_108,B_107] : k3_xboole_0(C_108,k4_xboole_0(B_107,C_108)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_501])).

tff(c_198,plain,(
    ! [B_64] : k3_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_1073,plain,(
    ! [C_109,B_110] : k3_xboole_0(C_109,k4_xboole_0(B_110,C_109)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_501])).

tff(c_1087,plain,(
    ! [C_109,B_110] : k4_xboole_0(C_109,k4_xboole_0(B_110,C_109)) = k5_xboole_0(C_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_14])).

tff(c_1147,plain,(
    ! [C_111,B_112] : k4_xboole_0(C_111,k4_xboole_0(B_112,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1087])).

tff(c_1156,plain,(
    ! [B_112,C_111] : k3_xboole_0(k4_xboole_0(B_112,C_111),C_111) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_991])).

tff(c_1246,plain,(
    ! [A_113,B_114] : k5_xboole_0(k2_xboole_0(A_113,B_114),k3_xboole_0(k5_xboole_0(A_113,B_114),k3_xboole_0(A_113,B_114))) = k2_xboole_0(k5_xboole_0(A_113,B_114),k3_xboole_0(A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_30])).

tff(c_23548,plain,(
    ! [A_378,B_379] : k5_xboole_0(k2_xboole_0(A_378,B_379),k3_xboole_0(k3_xboole_0(A_378,B_379),k5_xboole_0(A_378,B_379))) = k2_xboole_0(k5_xboole_0(A_378,B_379),k3_xboole_0(A_378,B_379)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1246])).

tff(c_23815,plain,(
    ! [B_112,C_111] : k5_xboole_0(k2_xboole_0(k4_xboole_0(B_112,C_111),C_111),k3_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(B_112,C_111),C_111))) = k2_xboole_0(k5_xboole_0(k4_xboole_0(B_112,C_111),C_111),k3_xboole_0(k4_xboole_0(B_112,C_111),C_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_23548])).

tff(c_23935,plain,(
    ! [B_112,C_111] : k2_xboole_0(k4_xboole_0(B_112,C_111),C_111) = k2_xboole_0(C_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5392,c_4066,c_1307,c_991,c_26,c_198,c_2,c_23815])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35657,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23935,c_48])).

tff(c_35852,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4287,c_35657])).

tff(c_35856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_35852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.44/5.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.44/5.25  
% 11.44/5.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.44/5.25  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 11.44/5.25  
% 11.44/5.25  %Foreground sorts:
% 11.44/5.25  
% 11.44/5.25  
% 11.44/5.25  %Background operators:
% 11.44/5.25  
% 11.44/5.25  
% 11.44/5.25  %Foreground operators:
% 11.44/5.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.44/5.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.44/5.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.44/5.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.44/5.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.44/5.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.44/5.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.44/5.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.44/5.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.44/5.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.44/5.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.44/5.25  tff('#skF_2', type, '#skF_2': $i).
% 11.44/5.25  tff('#skF_1', type, '#skF_1': $i).
% 11.44/5.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.44/5.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.44/5.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.44/5.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.44/5.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.44/5.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.44/5.25  
% 11.44/5.27  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 11.44/5.27  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.44/5.27  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.44/5.27  tff(f_73, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 11.44/5.27  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.44/5.27  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.44/5.27  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.44/5.27  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.44/5.27  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.44/5.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.44/5.27  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.44/5.27  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.44/5.27  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.44/5.27  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.44/5.27  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.44/5.27  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.44/5.27  tff(c_26, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.44/5.27  tff(c_898, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.44/5.27  tff(c_46, plain, (![A_40]: (r1_tarski(A_40, k1_zfmisc_1(k3_tarski(A_40))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.44/5.27  tff(c_139, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.44/5.27  tff(c_157, plain, (![A_40]: (k4_xboole_0(A_40, k1_zfmisc_1(k3_tarski(A_40)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_139])).
% 11.44/5.27  tff(c_160, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.44/5.27  tff(c_178, plain, (![A_40]: (k3_xboole_0(A_40, k1_zfmisc_1(k3_tarski(A_40)))=A_40)), inference(resolution, [status(thm)], [c_46, c_160])).
% 11.44/5.27  tff(c_574, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.44/5.27  tff(c_583, plain, (![A_40]: (k4_xboole_0(A_40, k1_zfmisc_1(k3_tarski(A_40)))=k5_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_178, c_574])).
% 11.44/5.27  tff(c_601, plain, (![A_40]: (k5_xboole_0(A_40, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_583])).
% 11.44/5.27  tff(c_3954, plain, (![A_179, B_180]: (k5_xboole_0(A_179, k5_xboole_0(B_180, k5_xboole_0(A_179, B_180)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_898, c_601])).
% 11.44/5.27  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.44/5.27  tff(c_181, plain, (![B_63]: (k4_xboole_0(B_63, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_139])).
% 11.44/5.27  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.44/5.27  tff(c_191, plain, (![B_64]: (r1_tarski(k1_xboole_0, B_64))), inference(superposition, [status(thm), theory('equality')], [c_181, c_18])).
% 11.44/5.27  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.44/5.27  tff(c_224, plain, (![B_68]: (k3_xboole_0(k1_xboole_0, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_191, c_16])).
% 11.44/5.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.44/5.27  tff(c_233, plain, (![B_68]: (k3_xboole_0(B_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_2])).
% 11.44/5.27  tff(c_1243, plain, (![A_113, B_114]: (k5_xboole_0(k5_xboole_0(A_113, B_114), k3_xboole_0(A_113, B_114))=k2_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.44/5.27  tff(c_1298, plain, (![A_20]: (k5_xboole_0(A_20, k3_xboole_0(A_20, k1_xboole_0))=k2_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1243])).
% 11.44/5.27  tff(c_1307, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_233, c_1298])).
% 11.44/5.27  tff(c_159, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_139])).
% 11.44/5.27  tff(c_675, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.44/5.27  tff(c_699, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_159, c_675])).
% 11.44/5.27  tff(c_1310, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_699])).
% 11.44/5.27  tff(c_180, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_160])).
% 11.44/5.27  tff(c_1289, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_180, c_1243])).
% 11.44/5.27  tff(c_1306, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_1289])).
% 11.44/5.27  tff(c_1425, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_1306])).
% 11.44/5.27  tff(c_925, plain, (![A_40, C_103]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_601, c_898])).
% 11.44/5.27  tff(c_3880, plain, (![A_40, C_103]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_925])).
% 11.44/5.27  tff(c_3962, plain, (![B_180, A_179]: (k5_xboole_0(B_180, k5_xboole_0(A_179, B_180))=k5_xboole_0(A_179, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3954, c_3880])).
% 11.44/5.27  tff(c_4039, plain, (![B_180, A_179]: (k5_xboole_0(B_180, k5_xboole_0(A_179, B_180))=A_179)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3962])).
% 11.44/5.27  tff(c_28, plain, (![A_21, B_22, C_23]: (k5_xboole_0(k5_xboole_0(A_21, B_22), C_23)=k5_xboole_0(A_21, k5_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.44/5.27  tff(c_42, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.44/5.27  tff(c_4140, plain, (![A_183, B_184]: (k3_xboole_0(k1_tarski(A_183), B_184)=k1_tarski(A_183) | ~r2_hidden(A_183, B_184))), inference(resolution, [status(thm)], [c_42, c_160])).
% 11.44/5.27  tff(c_30, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.44/5.27  tff(c_4193, plain, (![A_183, B_184]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_183), B_184), k1_tarski(A_183))=k2_xboole_0(k1_tarski(A_183), B_184) | ~r2_hidden(A_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_4140, c_30])).
% 11.44/5.27  tff(c_4287, plain, (![A_183, B_184]: (k2_xboole_0(k1_tarski(A_183), B_184)=B_184 | ~r2_hidden(A_183, B_184))), inference(demodulation, [status(thm), theory('equality')], [c_4039, c_28, c_4193])).
% 11.44/5.27  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.44/5.27  tff(c_5215, plain, (![B_198, A_199]: (k5_xboole_0(k5_xboole_0(B_198, A_199), k3_xboole_0(A_199, B_198))=k2_xboole_0(B_198, A_199))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1243])).
% 11.44/5.27  tff(c_5341, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k5_xboole_0(B_22, k3_xboole_0(B_22, A_21)))=k2_xboole_0(A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5215])).
% 11.44/5.27  tff(c_5392, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5341])).
% 11.44/5.27  tff(c_4057, plain, (![B_181, A_182]: (k5_xboole_0(B_181, k5_xboole_0(A_182, B_181))=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3962])).
% 11.44/5.27  tff(c_4066, plain, (![B_181, A_182]: (k5_xboole_0(B_181, A_182)=k5_xboole_0(A_182, B_181))), inference(superposition, [status(thm), theory('equality')], [c_4057, c_3880])).
% 11.44/5.27  tff(c_980, plain, (![A_106, B_107, C_108]: (k4_xboole_0(k3_xboole_0(A_106, B_107), C_108)=k3_xboole_0(A_106, k4_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.44/5.27  tff(c_393, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.44/5.27  tff(c_469, plain, (![A_78, B_79]: (r1_tarski(k3_xboole_0(A_78, B_79), A_78))), inference(superposition, [status(thm), theory('equality')], [c_393, c_18])).
% 11.44/5.27  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.44/5.27  tff(c_501, plain, (![A_78, B_79]: (k4_xboole_0(k3_xboole_0(A_78, B_79), A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_469, c_12])).
% 11.44/5.27  tff(c_991, plain, (![C_108, B_107]: (k3_xboole_0(C_108, k4_xboole_0(B_107, C_108))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_980, c_501])).
% 11.44/5.27  tff(c_198, plain, (![B_64]: (k3_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_191, c_16])).
% 11.44/5.27  tff(c_1073, plain, (![C_109, B_110]: (k3_xboole_0(C_109, k4_xboole_0(B_110, C_109))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_980, c_501])).
% 11.44/5.27  tff(c_1087, plain, (![C_109, B_110]: (k4_xboole_0(C_109, k4_xboole_0(B_110, C_109))=k5_xboole_0(C_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_14])).
% 11.44/5.27  tff(c_1147, plain, (![C_111, B_112]: (k4_xboole_0(C_111, k4_xboole_0(B_112, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1087])).
% 11.44/5.27  tff(c_1156, plain, (![B_112, C_111]: (k3_xboole_0(k4_xboole_0(B_112, C_111), C_111)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1147, c_991])).
% 11.44/5.27  tff(c_1246, plain, (![A_113, B_114]: (k5_xboole_0(k2_xboole_0(A_113, B_114), k3_xboole_0(k5_xboole_0(A_113, B_114), k3_xboole_0(A_113, B_114)))=k2_xboole_0(k5_xboole_0(A_113, B_114), k3_xboole_0(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_1243, c_30])).
% 11.44/5.27  tff(c_23548, plain, (![A_378, B_379]: (k5_xboole_0(k2_xboole_0(A_378, B_379), k3_xboole_0(k3_xboole_0(A_378, B_379), k5_xboole_0(A_378, B_379)))=k2_xboole_0(k5_xboole_0(A_378, B_379), k3_xboole_0(A_378, B_379)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1246])).
% 11.44/5.27  tff(c_23815, plain, (![B_112, C_111]: (k5_xboole_0(k2_xboole_0(k4_xboole_0(B_112, C_111), C_111), k3_xboole_0(k1_xboole_0, k5_xboole_0(k4_xboole_0(B_112, C_111), C_111)))=k2_xboole_0(k5_xboole_0(k4_xboole_0(B_112, C_111), C_111), k3_xboole_0(k4_xboole_0(B_112, C_111), C_111)))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_23548])).
% 11.44/5.27  tff(c_23935, plain, (![B_112, C_111]: (k2_xboole_0(k4_xboole_0(B_112, C_111), C_111)=k2_xboole_0(C_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_5392, c_4066, c_1307, c_991, c_26, c_198, c_2, c_23815])).
% 11.44/5.27  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.44/5.27  tff(c_35657, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23935, c_48])).
% 11.44/5.27  tff(c_35852, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4287, c_35657])).
% 11.44/5.27  tff(c_35856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_35852])).
% 11.44/5.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.44/5.27  
% 11.44/5.27  Inference rules
% 11.44/5.27  ----------------------
% 11.44/5.27  #Ref     : 0
% 11.44/5.27  #Sup     : 8919
% 11.44/5.27  #Fact    : 0
% 11.44/5.27  #Define  : 0
% 11.44/5.27  #Split   : 2
% 11.44/5.27  #Chain   : 0
% 11.44/5.27  #Close   : 0
% 11.44/5.27  
% 11.44/5.27  Ordering : KBO
% 11.44/5.27  
% 11.44/5.27  Simplification rules
% 11.44/5.27  ----------------------
% 11.44/5.27  #Subsume      : 252
% 11.44/5.27  #Demod        : 11025
% 11.44/5.27  #Tautology    : 6045
% 11.44/5.27  #SimpNegUnit  : 0
% 11.44/5.27  #BackRed      : 11
% 11.44/5.27  
% 11.44/5.27  #Partial instantiations: 0
% 11.44/5.27  #Strategies tried      : 1
% 11.44/5.27  
% 11.44/5.27  Timing (in seconds)
% 11.44/5.27  ----------------------
% 11.44/5.27  Preprocessing        : 0.33
% 11.44/5.27  Parsing              : 0.18
% 11.44/5.27  CNF conversion       : 0.02
% 11.44/5.27  Main loop            : 4.09
% 11.44/5.27  Inferencing          : 0.72
% 11.44/5.27  Reduction            : 2.44
% 11.44/5.27  Demodulation         : 2.18
% 11.44/5.27  BG Simplification    : 0.09
% 11.44/5.27  Subsumption          : 0.63
% 11.44/5.27  Abstraction          : 0.17
% 11.44/5.27  MUC search           : 0.00
% 11.44/5.27  Cooper               : 0.00
% 11.44/5.27  Total                : 4.45
% 11.44/5.27  Index Insertion      : 0.00
% 11.44/5.27  Index Deletion       : 0.00
% 11.44/5.27  Index Matching       : 0.00
% 11.44/5.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
