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
% DateTime   : Thu Dec  3 09:51:32 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  129 (1031 expanded)
%              Number of leaves         :   46 ( 367 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 (1028 expanded)
%              Number of equality atoms :   84 ( 984 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_95,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_96,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_702,plain,(
    ! [A_113,B_114] : k5_xboole_0(k5_xboole_0(A_113,B_114),k3_xboole_0(A_113,B_114)) = k2_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_759,plain,(
    ! [A_18] : k5_xboole_0(k5_xboole_0(A_18,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_702])).

tff(c_774,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_759])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_837,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k5_xboole_0(A_118,B_119),C_120) = k5_xboole_0(A_118,k5_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3297,plain,(
    ! [A_208,B_209,C_210] : k5_xboole_0(k5_xboole_0(A_208,B_209),C_210) = k5_xboole_0(B_209,k5_xboole_0(A_208,C_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_837])).

tff(c_30,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3389,plain,(
    ! [B_209,A_208] : k5_xboole_0(B_209,k5_xboole_0(A_208,k3_xboole_0(A_208,B_209))) = k2_xboole_0(A_208,B_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_3297,c_30])).

tff(c_3546,plain,(
    ! [B_211,A_212] : k5_xboole_0(B_211,k4_xboole_0(A_212,B_211)) = k2_xboole_0(A_212,B_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3389])).

tff(c_125,plain,(
    ! [B_72,A_73] : k5_xboole_0(B_72,A_73) = k5_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_22])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_920,plain,(
    ! [A_26,C_120] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_120)) = k5_xboole_0(k1_xboole_0,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_837])).

tff(c_933,plain,(
    ! [A_26,C_120] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_920])).

tff(c_5903,plain,(
    ! [B_255,A_256] : k5_xboole_0(B_255,k2_xboole_0(A_256,B_255)) = k4_xboole_0(A_256,B_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_3546,c_933])).

tff(c_6041,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_5903])).

tff(c_6061,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6041])).

tff(c_944,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_920])).

tff(c_1046,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k5_xboole_0(B_127,A_126)) = B_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_944])).

tff(c_1088,plain,(
    ! [A_26,C_120] : k5_xboole_0(k5_xboole_0(A_26,C_120),C_120) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_1046])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2262,plain,(
    ! [A_194,B_195] : k5_xboole_0(A_194,k4_xboole_0(A_194,B_195)) = k3_xboole_0(A_194,B_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_944])).

tff(c_2340,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2262])).

tff(c_4006,plain,(
    ! [A_217,B_218] : k3_xboole_0(A_217,k4_xboole_0(A_217,B_218)) = k4_xboole_0(A_217,B_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2340])).

tff(c_4048,plain,(
    ! [A_217,B_218] : k5_xboole_0(k5_xboole_0(A_217,k4_xboole_0(A_217,B_218)),k4_xboole_0(A_217,B_218)) = k2_xboole_0(A_217,k4_xboole_0(A_217,B_218)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4006,c_30])).

tff(c_4100,plain,(
    ! [A_217,B_218] : k2_xboole_0(A_217,k4_xboole_0(A_217,B_218)) = A_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_4048])).

tff(c_6080,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6061,c_4100])).

tff(c_6116,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6080])).

tff(c_3526,plain,(
    ! [B_209,A_208] : k5_xboole_0(B_209,k4_xboole_0(A_208,B_209)) = k2_xboole_0(A_208,B_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3389])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_526,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_548,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_526])).

tff(c_850,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k5_xboole_0(B_119,k3_xboole_0(A_118,B_119))) = k2_xboole_0(A_118,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_30])).

tff(c_4244,plain,(
    ! [B_225,A_226] : k2_xboole_0(B_225,A_226) = k2_xboole_0(A_226,B_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_548,c_850])).

tff(c_4275,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4244,c_64])).

tff(c_6405,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6116,c_4275])).

tff(c_6407,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_6405])).

tff(c_558,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_526])).

tff(c_565,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_558])).

tff(c_566,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_558])).

tff(c_572,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k3_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_20])).

tff(c_610,plain,(
    ! [A_107] : k4_xboole_0(A_107,A_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_572])).

tff(c_622,plain,(
    ! [A_107] : k4_xboole_0(A_107,k1_xboole_0) = k3_xboole_0(A_107,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_20])).

tff(c_650,plain,(
    ! [A_111] : k3_xboole_0(A_111,A_111) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_622])).

tff(c_222,plain,(
    ! [B_75,A_76] : k3_xboole_0(B_75,A_76) = k3_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [B_75,A_76] : r1_tarski(k3_xboole_0(B_75,A_76),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_16])).

tff(c_668,plain,(
    ! [A_111] : r1_tarski(A_111,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_237])).

tff(c_24,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_422,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_438,plain,(
    ! [A_18,C_94] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_422])).

tff(c_441,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_438])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_376,plain,(
    ! [C_88,A_89] :
      ( r1_tarski(C_88,A_89)
      | ~ r2_hidden(C_88,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1415,plain,(
    ! [C_143] :
      ( r1_tarski(C_143,k1_xboole_0)
      | ~ r2_hidden(C_143,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_376])).

tff(c_1424,plain,
    ( r1_tarski('#skF_2'(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1415])).

tff(c_2077,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1424])).

tff(c_343,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(C_83,k1_zfmisc_1(A_84))
      | ~ r1_tarski(C_83,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_346,plain,(
    ! [C_83] :
      ( r2_hidden(C_83,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_343])).

tff(c_2079,plain,(
    ! [C_83] :
      ( r2_hidden(C_83,k1_xboole_0)
      | ~ r1_tarski(C_83,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2077,c_346])).

tff(c_2090,plain,(
    ! [C_188] : ~ r1_tarski(C_188,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_2079])).

tff(c_2116,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_668,c_2090])).

tff(c_2118,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1424])).

tff(c_6428,plain,(
    k1_tarski('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6407,c_6407,c_2118])).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6450,plain,(
    k3_tarski('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6407,c_6407,c_62])).

tff(c_635,plain,(
    ! [A_107] : k3_xboole_0(A_107,A_107) = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_622])).

tff(c_765,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_26,A_26)) = k2_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_702])).

tff(c_776,plain,(
    ! [A_26] : k2_xboole_0(A_26,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_635,c_765])).

tff(c_32,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_347,plain,(
    ! [A_85,B_86] : k3_tarski(k2_tarski(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_356,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = k2_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_347])).

tff(c_807,plain,(
    ! [A_29] : k3_tarski(k1_tarski(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_356])).

tff(c_6412,plain,(
    k3_tarski(k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6116,c_807])).

tff(c_6579,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6450,c_6407,c_6412])).

tff(c_6416,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6407,c_6116])).

tff(c_6580,plain,(
    k1_tarski('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6579,c_6416])).

tff(c_6582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6428,c_6580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.18  
% 5.96/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 5.96/2.18  
% 5.96/2.18  %Foreground sorts:
% 5.96/2.18  
% 5.96/2.18  
% 5.96/2.18  %Background operators:
% 5.96/2.18  
% 5.96/2.18  
% 5.96/2.18  %Foreground operators:
% 5.96/2.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.96/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.96/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.96/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.96/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.96/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.96/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.96/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.96/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.96/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.96/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.96/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.96/2.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.96/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.96/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.96/2.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.96/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.96/2.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.96/2.18  
% 5.96/2.21  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.96/2.21  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.96/2.21  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.96/2.21  tff(f_100, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.96/2.21  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.96/2.21  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.96/2.21  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.96/2.21  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.96/2.21  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.96/2.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.96/2.21  tff(f_57, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.96/2.21  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.96/2.21  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.96/2.21  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.96/2.21  tff(f_95, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 5.96/2.21  tff(f_92, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.96/2.21  tff(f_96, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 5.96/2.21  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.96/2.21  tff(f_94, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.96/2.21  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.96/2.21  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.96/2.21  tff(c_702, plain, (![A_113, B_114]: (k5_xboole_0(k5_xboole_0(A_113, B_114), k3_xboole_0(A_113, B_114))=k2_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.96/2.21  tff(c_759, plain, (![A_18]: (k5_xboole_0(k5_xboole_0(A_18, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_702])).
% 5.96/2.21  tff(c_774, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_759])).
% 5.96/2.21  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.96/2.21  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.96/2.21  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.96/2.21  tff(c_837, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k5_xboole_0(A_118, B_119), C_120)=k5_xboole_0(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.96/2.21  tff(c_3297, plain, (![A_208, B_209, C_210]: (k5_xboole_0(k5_xboole_0(A_208, B_209), C_210)=k5_xboole_0(B_209, k5_xboole_0(A_208, C_210)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_837])).
% 5.96/2.21  tff(c_30, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.96/2.21  tff(c_3389, plain, (![B_209, A_208]: (k5_xboole_0(B_209, k5_xboole_0(A_208, k3_xboole_0(A_208, B_209)))=k2_xboole_0(A_208, B_209))), inference(superposition, [status(thm), theory('equality')], [c_3297, c_30])).
% 5.96/2.21  tff(c_3546, plain, (![B_211, A_212]: (k5_xboole_0(B_211, k4_xboole_0(A_212, B_211))=k2_xboole_0(A_212, B_211))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3389])).
% 5.96/2.21  tff(c_125, plain, (![B_72, A_73]: (k5_xboole_0(B_72, A_73)=k5_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.96/2.21  tff(c_141, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_125, c_22])).
% 5.96/2.21  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.96/2.21  tff(c_920, plain, (![A_26, C_120]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_120))=k5_xboole_0(k1_xboole_0, C_120))), inference(superposition, [status(thm), theory('equality')], [c_28, c_837])).
% 5.96/2.21  tff(c_933, plain, (![A_26, C_120]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_920])).
% 5.96/2.21  tff(c_5903, plain, (![B_255, A_256]: (k5_xboole_0(B_255, k2_xboole_0(A_256, B_255))=k4_xboole_0(A_256, B_255))), inference(superposition, [status(thm), theory('equality')], [c_3546, c_933])).
% 5.96/2.21  tff(c_6041, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_5903])).
% 5.96/2.21  tff(c_6061, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6041])).
% 5.96/2.21  tff(c_944, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_920])).
% 5.96/2.21  tff(c_1046, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k5_xboole_0(B_127, A_126))=B_127)), inference(superposition, [status(thm), theory('equality')], [c_4, c_944])).
% 5.96/2.21  tff(c_1088, plain, (![A_26, C_120]: (k5_xboole_0(k5_xboole_0(A_26, C_120), C_120)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_933, c_1046])).
% 5.96/2.21  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.96/2.21  tff(c_2262, plain, (![A_194, B_195]: (k5_xboole_0(A_194, k4_xboole_0(A_194, B_195))=k3_xboole_0(A_194, B_195))), inference(superposition, [status(thm), theory('equality')], [c_14, c_944])).
% 5.96/2.21  tff(c_2340, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k3_xboole_0(A_19, k4_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2262])).
% 5.96/2.21  tff(c_4006, plain, (![A_217, B_218]: (k3_xboole_0(A_217, k4_xboole_0(A_217, B_218))=k4_xboole_0(A_217, B_218))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2340])).
% 5.96/2.21  tff(c_4048, plain, (![A_217, B_218]: (k5_xboole_0(k5_xboole_0(A_217, k4_xboole_0(A_217, B_218)), k4_xboole_0(A_217, B_218))=k2_xboole_0(A_217, k4_xboole_0(A_217, B_218)))), inference(superposition, [status(thm), theory('equality')], [c_4006, c_30])).
% 5.96/2.21  tff(c_4100, plain, (![A_217, B_218]: (k2_xboole_0(A_217, k4_xboole_0(A_217, B_218))=A_217)), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_4048])).
% 5.96/2.21  tff(c_6080, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6061, c_4100])).
% 5.96/2.21  tff(c_6116, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6080])).
% 5.96/2.21  tff(c_3526, plain, (![B_209, A_208]: (k5_xboole_0(B_209, k4_xboole_0(A_208, B_209))=k2_xboole_0(A_208, B_209))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3389])).
% 5.96/2.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.96/2.21  tff(c_526, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.96/2.21  tff(c_548, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_526])).
% 5.96/2.21  tff(c_850, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k5_xboole_0(B_119, k3_xboole_0(A_118, B_119)))=k2_xboole_0(A_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_837, c_30])).
% 5.96/2.21  tff(c_4244, plain, (![B_225, A_226]: (k2_xboole_0(B_225, A_226)=k2_xboole_0(A_226, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_548, c_850])).
% 5.96/2.21  tff(c_4275, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4244, c_64])).
% 5.96/2.21  tff(c_6405, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6116, c_4275])).
% 5.96/2.21  tff(c_6407, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_6405])).
% 5.96/2.21  tff(c_558, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_526])).
% 5.96/2.21  tff(c_565, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_558])).
% 5.96/2.21  tff(c_566, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_558])).
% 5.96/2.21  tff(c_572, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k3_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_566, c_20])).
% 5.96/2.21  tff(c_610, plain, (![A_107]: (k4_xboole_0(A_107, A_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_572])).
% 5.96/2.21  tff(c_622, plain, (![A_107]: (k4_xboole_0(A_107, k1_xboole_0)=k3_xboole_0(A_107, A_107))), inference(superposition, [status(thm), theory('equality')], [c_610, c_20])).
% 5.96/2.21  tff(c_650, plain, (![A_111]: (k3_xboole_0(A_111, A_111)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_565, c_622])).
% 5.96/2.21  tff(c_222, plain, (![B_75, A_76]: (k3_xboole_0(B_75, A_76)=k3_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.96/2.21  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.96/2.21  tff(c_237, plain, (![B_75, A_76]: (r1_tarski(k3_xboole_0(B_75, A_76), A_76))), inference(superposition, [status(thm), theory('equality')], [c_222, c_16])).
% 5.96/2.21  tff(c_668, plain, (![A_111]: (r1_tarski(A_111, A_111))), inference(superposition, [status(thm), theory('equality')], [c_650, c_237])).
% 5.96/2.21  tff(c_24, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.96/2.21  tff(c_422, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.96/2.21  tff(c_438, plain, (![A_18, C_94]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_422])).
% 5.96/2.21  tff(c_441, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_438])).
% 5.96/2.21  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.96/2.21  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.96/2.21  tff(c_376, plain, (![C_88, A_89]: (r1_tarski(C_88, A_89) | ~r2_hidden(C_88, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.96/2.21  tff(c_1415, plain, (![C_143]: (r1_tarski(C_143, k1_xboole_0) | ~r2_hidden(C_143, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_376])).
% 5.96/2.21  tff(c_1424, plain, (r1_tarski('#skF_2'(k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1415])).
% 5.96/2.21  tff(c_2077, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1424])).
% 5.96/2.21  tff(c_343, plain, (![C_83, A_84]: (r2_hidden(C_83, k1_zfmisc_1(A_84)) | ~r1_tarski(C_83, A_84))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.96/2.21  tff(c_346, plain, (![C_83]: (r2_hidden(C_83, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_343])).
% 5.96/2.21  tff(c_2079, plain, (![C_83]: (r2_hidden(C_83, k1_xboole_0) | ~r1_tarski(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2077, c_346])).
% 5.96/2.21  tff(c_2090, plain, (![C_188]: (~r1_tarski(C_188, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_441, c_2079])).
% 5.96/2.21  tff(c_2116, plain, $false, inference(resolution, [status(thm)], [c_668, c_2090])).
% 5.96/2.21  tff(c_2118, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1424])).
% 5.96/2.21  tff(c_6428, plain, (k1_tarski('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6407, c_6407, c_2118])).
% 5.96/2.21  tff(c_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.96/2.21  tff(c_6450, plain, (k3_tarski('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6407, c_6407, c_62])).
% 5.96/2.21  tff(c_635, plain, (![A_107]: (k3_xboole_0(A_107, A_107)=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_565, c_622])).
% 5.96/2.21  tff(c_765, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_26, A_26))=k2_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_702])).
% 5.96/2.21  tff(c_776, plain, (![A_26]: (k2_xboole_0(A_26, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_635, c_765])).
% 5.96/2.21  tff(c_32, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.96/2.21  tff(c_347, plain, (![A_85, B_86]: (k3_tarski(k2_tarski(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.96/2.21  tff(c_356, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=k2_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_32, c_347])).
% 5.96/2.21  tff(c_807, plain, (![A_29]: (k3_tarski(k1_tarski(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_776, c_356])).
% 5.96/2.21  tff(c_6412, plain, (k3_tarski(k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6116, c_807])).
% 5.96/2.21  tff(c_6579, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6450, c_6407, c_6412])).
% 5.96/2.21  tff(c_6416, plain, (k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6407, c_6116])).
% 5.96/2.21  tff(c_6580, plain, (k1_tarski('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6579, c_6416])).
% 5.96/2.21  tff(c_6582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6428, c_6580])).
% 5.96/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.21  
% 5.96/2.21  Inference rules
% 5.96/2.21  ----------------------
% 5.96/2.21  #Ref     : 0
% 5.96/2.21  #Sup     : 1641
% 5.96/2.21  #Fact    : 0
% 5.96/2.21  #Define  : 0
% 5.96/2.21  #Split   : 1
% 5.96/2.21  #Chain   : 0
% 5.96/2.21  #Close   : 0
% 5.96/2.21  
% 5.96/2.21  Ordering : KBO
% 5.96/2.21  
% 5.96/2.21  Simplification rules
% 5.96/2.21  ----------------------
% 5.96/2.21  #Subsume      : 42
% 5.96/2.21  #Demod        : 1654
% 5.96/2.21  #Tautology    : 960
% 5.96/2.21  #SimpNegUnit  : 11
% 5.96/2.21  #BackRed      : 43
% 5.96/2.21  
% 5.96/2.21  #Partial instantiations: 0
% 5.96/2.21  #Strategies tried      : 1
% 5.96/2.21  
% 5.96/2.21  Timing (in seconds)
% 5.96/2.21  ----------------------
% 5.96/2.21  Preprocessing        : 0.33
% 5.96/2.21  Parsing              : 0.18
% 5.96/2.21  CNF conversion       : 0.02
% 5.96/2.21  Main loop            : 1.08
% 5.96/2.21  Inferencing          : 0.28
% 5.96/2.21  Reduction            : 0.55
% 5.96/2.21  Demodulation         : 0.47
% 5.96/2.21  BG Simplification    : 0.04
% 5.96/2.21  Subsumption          : 0.15
% 5.96/2.21  Abstraction          : 0.05
% 5.96/2.21  MUC search           : 0.00
% 5.96/2.21  Cooper               : 0.00
% 5.96/2.21  Total                : 1.47
% 5.96/2.21  Index Insertion      : 0.00
% 5.96/2.21  Index Deletion       : 0.00
% 5.96/2.21  Index Matching       : 0.00
% 5.96/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
