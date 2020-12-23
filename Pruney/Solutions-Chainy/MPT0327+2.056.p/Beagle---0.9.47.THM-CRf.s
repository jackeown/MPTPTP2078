%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:38 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  108 (1101 expanded)
%              Number of leaves         :   34 ( 386 expanded)
%              Depth                    :   18
%              Number of atoms          :  101 (1356 expanded)
%              Number of equality atoms :   78 ( 954 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_73,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_564,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_608,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_564])).

tff(c_618,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_608])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_623,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_12])).

tff(c_641,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_623])).

tff(c_224,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tarski(A_67),B_68)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_234,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(k1_tarski(A_67),B_68) = k1_xboole_0
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_131])).

tff(c_576,plain,(
    ! [A_89,B_90] : k4_xboole_0(k3_xboole_0(A_89,B_90),A_89) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_146])).

tff(c_1131,plain,(
    ! [A_119,B_120,C_121] : k4_xboole_0(k3_xboole_0(A_119,B_120),C_121) = k3_xboole_0(A_119,k4_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1178,plain,(
    ! [A_89,B_90] : k3_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_1131])).

tff(c_1024,plain,(
    ! [A_114,B_115] : k5_xboole_0(k5_xboole_0(A_114,B_115),k3_xboole_0(A_114,B_115)) = k2_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5449,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k5_xboole_0(B_213,k3_xboole_0(A_212,B_213))) = k2_xboole_0(A_212,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_26])).

tff(c_5528,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k5_xboole_0(k4_xboole_0(B_90,A_89),k1_xboole_0)) = k2_xboole_0(A_89,k4_xboole_0(B_90,A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_5449])).

tff(c_6070,plain,(
    ! [A_224,B_225] : k5_xboole_0(A_224,k4_xboole_0(B_225,A_224)) = k2_xboole_0(A_224,B_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_18,c_5528])).

tff(c_6141,plain,(
    ! [B_68,A_67] :
      ( k2_xboole_0(B_68,k1_tarski(A_67)) = k5_xboole_0(B_68,k1_xboole_0)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_6070])).

tff(c_6178,plain,(
    ! [B_68,A_67] :
      ( k2_xboole_0(B_68,k1_tarski(A_67)) = B_68
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_6141])).

tff(c_46,plain,(
    ! [A_43] : r1_tarski(A_43,k1_zfmisc_1(k3_tarski(A_43))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_zfmisc_1(k3_tarski(A_43))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_131])).

tff(c_96,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_43] : k3_xboole_0(A_43,k1_zfmisc_1(k3_tarski(A_43))) = A_43 ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_447,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_459,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_zfmisc_1(k3_tarski(A_43))) = k5_xboole_0(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_447])).

tff(c_466,plain,(
    ! [A_43] : k5_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_459])).

tff(c_781,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_819,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k5_xboole_0(B_103,k5_xboole_0(A_102,B_103))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_781])).

tff(c_617,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_608])).

tff(c_1058,plain,(
    ! [A_13] : k5_xboole_0(k5_xboole_0(A_13,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_1024])).

tff(c_1077,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_641,c_1058])).

tff(c_392,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(B_79,A_78)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_410,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = k2_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_392])).

tff(c_1083,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_410])).

tff(c_112,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_1073,plain,(
    ! [B_2] : k5_xboole_0(k5_xboole_0(B_2,B_2),B_2) = k2_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1024])).

tff(c_1079,plain,(
    ! [B_2] : k5_xboole_0(k1_xboole_0,B_2) = k2_xboole_0(B_2,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_1073])).

tff(c_1277,plain,(
    ! [B_2] : k5_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1079])).

tff(c_815,plain,(
    ! [A_43,C_104] : k5_xboole_0(A_43,k5_xboole_0(A_43,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_781])).

tff(c_3390,plain,(
    ! [A_180,C_181] : k5_xboole_0(A_180,k5_xboole_0(A_180,C_181)) = C_181 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_815])).

tff(c_3430,plain,(
    ! [B_103,A_102] : k5_xboole_0(B_103,k5_xboole_0(A_102,B_103)) = k5_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_3390])).

tff(c_3474,plain,(
    ! [B_103,A_102] : k5_xboole_0(B_103,k5_xboole_0(A_102,B_103)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_3430])).

tff(c_401,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_392])).

tff(c_2402,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_401])).

tff(c_1202,plain,(
    ! [B_2,C_121] : k3_xboole_0(B_2,k4_xboole_0(B_2,C_121)) = k4_xboole_0(B_2,C_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1131])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2276,plain,(
    ! [B_159,C_160] : k3_xboole_0(B_159,k4_xboole_0(B_159,C_160)) = k4_xboole_0(B_159,C_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1131])).

tff(c_2314,plain,(
    ! [B_159,C_160] : k5_xboole_0(B_159,k4_xboole_0(B_159,C_160)) = k4_xboole_0(B_159,k4_xboole_0(B_159,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_12])).

tff(c_2967,plain,(
    ! [B_172,C_173] : k5_xboole_0(B_172,k4_xboole_0(B_172,C_173)) = k3_xboole_0(B_172,C_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2314])).

tff(c_28,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2977,plain,(
    ! [B_172,C_173] : k5_xboole_0(k3_xboole_0(B_172,C_173),k3_xboole_0(B_172,k4_xboole_0(B_172,C_173))) = k2_xboole_0(B_172,k4_xboole_0(B_172,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2967,c_28])).

tff(c_3040,plain,(
    ! [B_172,C_173] : k5_xboole_0(k3_xboole_0(B_172,C_173),k4_xboole_0(B_172,C_173)) = B_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2402,c_1202,c_2977])).

tff(c_13530,plain,(
    ! [A_310,B_311,C_312] : k5_xboole_0(k5_xboole_0(A_310,B_311),k5_xboole_0(k3_xboole_0(A_310,B_311),C_312)) = k5_xboole_0(k2_xboole_0(A_310,B_311),C_312) ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_26])).

tff(c_13651,plain,(
    ! [B_172,C_173] : k5_xboole_0(k2_xboole_0(B_172,C_173),k4_xboole_0(B_172,C_173)) = k5_xboole_0(k5_xboole_0(B_172,C_173),B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_3040,c_13530])).

tff(c_13933,plain,(
    ! [B_315,C_316] : k5_xboole_0(k2_xboole_0(B_315,C_316),k4_xboole_0(B_315,C_316)) = C_316 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_26,c_13651])).

tff(c_3389,plain,(
    ! [A_43,C_104] : k5_xboole_0(A_43,k5_xboole_0(A_43,C_104)) = C_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_815])).

tff(c_3486,plain,(
    ! [B_182,A_183] : k5_xboole_0(B_182,k5_xboole_0(A_183,B_182)) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_3430])).

tff(c_3522,plain,(
    ! [A_43,C_104] : k5_xboole_0(k5_xboole_0(A_43,C_104),C_104) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_3389,c_3486])).

tff(c_15258,plain,(
    ! [C_328,B_329] : k5_xboole_0(C_328,k4_xboole_0(B_329,C_328)) = k2_xboole_0(B_329,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_13933,c_3522])).

tff(c_5582,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = k2_xboole_0(A_89,B_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_18,c_5528])).

tff(c_15275,plain,(
    ! [C_328,B_329] : k2_xboole_0(C_328,B_329) = k2_xboole_0(B_329,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_15258,c_5582])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15421,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_48])).

tff(c_15422,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_18,c_15421])).

tff(c_16102,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_15422])).

tff(c_16106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:26:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.91  
% 7.59/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.91  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.59/2.91  
% 7.59/2.91  %Foreground sorts:
% 7.59/2.91  
% 7.59/2.91  
% 7.59/2.91  %Background operators:
% 7.59/2.91  
% 7.59/2.91  
% 7.59/2.91  %Foreground operators:
% 7.59/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.59/2.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.59/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.59/2.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.59/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.59/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.59/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.59/2.91  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.91  tff('#skF_1', type, '#skF_1': $i).
% 7.59/2.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.59/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.59/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.59/2.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.59/2.91  
% 7.59/2.93  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 7.59/2.93  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.59/2.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.59/2.93  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.59/2.93  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.59/2.93  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.59/2.93  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.59/2.93  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.59/2.93  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.59/2.93  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.59/2.93  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.59/2.93  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.59/2.93  tff(f_73, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.59/2.93  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.59/2.93  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.59/2.93  tff(c_20, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.59/2.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.93  tff(c_131, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.93  tff(c_147, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_131])).
% 7.59/2.93  tff(c_564, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.59/2.93  tff(c_608, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_564])).
% 7.59/2.93  tff(c_618, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_608])).
% 7.59/2.93  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.59/2.93  tff(c_623, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_618, c_12])).
% 7.59/2.93  tff(c_641, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_623])).
% 7.59/2.93  tff(c_224, plain, (![A_67, B_68]: (r1_tarski(k1_tarski(A_67), B_68) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.59/2.93  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.93  tff(c_234, plain, (![A_67, B_68]: (k4_xboole_0(k1_tarski(A_67), B_68)=k1_xboole_0 | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_224, c_10])).
% 7.59/2.93  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.59/2.93  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.59/2.93  tff(c_146, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_131])).
% 7.59/2.93  tff(c_576, plain, (![A_89, B_90]: (k4_xboole_0(k3_xboole_0(A_89, B_90), A_89)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_564, c_146])).
% 7.59/2.93  tff(c_1131, plain, (![A_119, B_120, C_121]: (k4_xboole_0(k3_xboole_0(A_119, B_120), C_121)=k3_xboole_0(A_119, k4_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.59/2.93  tff(c_1178, plain, (![A_89, B_90]: (k3_xboole_0(A_89, k4_xboole_0(B_90, A_89))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_576, c_1131])).
% 7.59/2.93  tff(c_1024, plain, (![A_114, B_115]: (k5_xboole_0(k5_xboole_0(A_114, B_115), k3_xboole_0(A_114, B_115))=k2_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.59/2.93  tff(c_26, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.59/2.93  tff(c_5449, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k5_xboole_0(B_213, k3_xboole_0(A_212, B_213)))=k2_xboole_0(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_1024, c_26])).
% 7.59/2.93  tff(c_5528, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k5_xboole_0(k4_xboole_0(B_90, A_89), k1_xboole_0))=k2_xboole_0(A_89, k4_xboole_0(B_90, A_89)))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_5449])).
% 7.59/2.93  tff(c_6070, plain, (![A_224, B_225]: (k5_xboole_0(A_224, k4_xboole_0(B_225, A_224))=k2_xboole_0(A_224, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_18, c_5528])).
% 7.59/2.93  tff(c_6141, plain, (![B_68, A_67]: (k2_xboole_0(B_68, k1_tarski(A_67))=k5_xboole_0(B_68, k1_xboole_0) | ~r2_hidden(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_234, c_6070])).
% 7.59/2.93  tff(c_6178, plain, (![B_68, A_67]: (k2_xboole_0(B_68, k1_tarski(A_67))=B_68 | ~r2_hidden(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_6141])).
% 7.59/2.93  tff(c_46, plain, (![A_43]: (r1_tarski(A_43, k1_zfmisc_1(k3_tarski(A_43))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.59/2.93  tff(c_145, plain, (![A_43]: (k4_xboole_0(A_43, k1_zfmisc_1(k3_tarski(A_43)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_131])).
% 7.59/2.93  tff(c_96, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.59/2.93  tff(c_110, plain, (![A_43]: (k3_xboole_0(A_43, k1_zfmisc_1(k3_tarski(A_43)))=A_43)), inference(resolution, [status(thm)], [c_46, c_96])).
% 7.59/2.93  tff(c_447, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.59/2.93  tff(c_459, plain, (![A_43]: (k4_xboole_0(A_43, k1_zfmisc_1(k3_tarski(A_43)))=k5_xboole_0(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_110, c_447])).
% 7.59/2.93  tff(c_466, plain, (![A_43]: (k5_xboole_0(A_43, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_459])).
% 7.59/2.93  tff(c_781, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.59/2.93  tff(c_819, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k5_xboole_0(B_103, k5_xboole_0(A_102, B_103)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_466, c_781])).
% 7.59/2.93  tff(c_617, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_608])).
% 7.59/2.93  tff(c_1058, plain, (![A_13]: (k5_xboole_0(k5_xboole_0(A_13, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_617, c_1024])).
% 7.59/2.93  tff(c_1077, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_641, c_641, c_1058])).
% 7.59/2.93  tff(c_392, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(B_79, A_78))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.59/2.93  tff(c_410, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=k2_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_147, c_392])).
% 7.59/2.93  tff(c_1083, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_410])).
% 7.59/2.93  tff(c_112, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_96])).
% 7.59/2.93  tff(c_1073, plain, (![B_2]: (k5_xboole_0(k5_xboole_0(B_2, B_2), B_2)=k2_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1024])).
% 7.59/2.93  tff(c_1079, plain, (![B_2]: (k5_xboole_0(k1_xboole_0, B_2)=k2_xboole_0(B_2, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_1073])).
% 7.59/2.93  tff(c_1277, plain, (![B_2]: (k5_xboole_0(k1_xboole_0, B_2)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1079])).
% 7.59/2.93  tff(c_815, plain, (![A_43, C_104]: (k5_xboole_0(A_43, k5_xboole_0(A_43, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_466, c_781])).
% 7.59/2.93  tff(c_3390, plain, (![A_180, C_181]: (k5_xboole_0(A_180, k5_xboole_0(A_180, C_181))=C_181)), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_815])).
% 7.59/2.93  tff(c_3430, plain, (![B_103, A_102]: (k5_xboole_0(B_103, k5_xboole_0(A_102, B_103))=k5_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_819, c_3390])).
% 7.59/2.93  tff(c_3474, plain, (![B_103, A_102]: (k5_xboole_0(B_103, k5_xboole_0(A_102, B_103))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_641, c_3430])).
% 7.59/2.93  tff(c_401, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k2_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_146, c_392])).
% 7.59/2.93  tff(c_2402, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_401])).
% 7.59/2.93  tff(c_1202, plain, (![B_2, C_121]: (k3_xboole_0(B_2, k4_xboole_0(B_2, C_121))=k4_xboole_0(B_2, C_121))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1131])).
% 7.59/2.93  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.59/2.93  tff(c_2276, plain, (![B_159, C_160]: (k3_xboole_0(B_159, k4_xboole_0(B_159, C_160))=k4_xboole_0(B_159, C_160))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1131])).
% 7.59/2.93  tff(c_2314, plain, (![B_159, C_160]: (k5_xboole_0(B_159, k4_xboole_0(B_159, C_160))=k4_xboole_0(B_159, k4_xboole_0(B_159, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_2276, c_12])).
% 7.59/2.93  tff(c_2967, plain, (![B_172, C_173]: (k5_xboole_0(B_172, k4_xboole_0(B_172, C_173))=k3_xboole_0(B_172, C_173))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2314])).
% 7.59/2.93  tff(c_28, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.59/2.93  tff(c_2977, plain, (![B_172, C_173]: (k5_xboole_0(k3_xboole_0(B_172, C_173), k3_xboole_0(B_172, k4_xboole_0(B_172, C_173)))=k2_xboole_0(B_172, k4_xboole_0(B_172, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_2967, c_28])).
% 7.59/2.93  tff(c_3040, plain, (![B_172, C_173]: (k5_xboole_0(k3_xboole_0(B_172, C_173), k4_xboole_0(B_172, C_173))=B_172)), inference(demodulation, [status(thm), theory('equality')], [c_2402, c_1202, c_2977])).
% 7.59/2.93  tff(c_13530, plain, (![A_310, B_311, C_312]: (k5_xboole_0(k5_xboole_0(A_310, B_311), k5_xboole_0(k3_xboole_0(A_310, B_311), C_312))=k5_xboole_0(k2_xboole_0(A_310, B_311), C_312))), inference(superposition, [status(thm), theory('equality')], [c_1024, c_26])).
% 7.59/2.93  tff(c_13651, plain, (![B_172, C_173]: (k5_xboole_0(k2_xboole_0(B_172, C_173), k4_xboole_0(B_172, C_173))=k5_xboole_0(k5_xboole_0(B_172, C_173), B_172))), inference(superposition, [status(thm), theory('equality')], [c_3040, c_13530])).
% 7.59/2.93  tff(c_13933, plain, (![B_315, C_316]: (k5_xboole_0(k2_xboole_0(B_315, C_316), k4_xboole_0(B_315, C_316))=C_316)), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_26, c_13651])).
% 7.59/2.93  tff(c_3389, plain, (![A_43, C_104]: (k5_xboole_0(A_43, k5_xboole_0(A_43, C_104))=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_815])).
% 7.59/2.93  tff(c_3486, plain, (![B_182, A_183]: (k5_xboole_0(B_182, k5_xboole_0(A_183, B_182))=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_641, c_3430])).
% 7.59/2.93  tff(c_3522, plain, (![A_43, C_104]: (k5_xboole_0(k5_xboole_0(A_43, C_104), C_104)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_3389, c_3486])).
% 7.59/2.93  tff(c_15258, plain, (![C_328, B_329]: (k5_xboole_0(C_328, k4_xboole_0(B_329, C_328))=k2_xboole_0(B_329, C_328))), inference(superposition, [status(thm), theory('equality')], [c_13933, c_3522])).
% 7.59/2.93  tff(c_5582, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k4_xboole_0(B_90, A_89))=k2_xboole_0(A_89, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_18, c_5528])).
% 7.59/2.93  tff(c_15275, plain, (![C_328, B_329]: (k2_xboole_0(C_328, B_329)=k2_xboole_0(B_329, C_328))), inference(superposition, [status(thm), theory('equality')], [c_15258, c_5582])).
% 7.59/2.93  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.59/2.93  tff(c_15421, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_48])).
% 7.59/2.93  tff(c_15422, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_18, c_15421])).
% 7.59/2.93  tff(c_16102, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6178, c_15422])).
% 7.59/2.93  tff(c_16106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_16102])).
% 7.59/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.93  
% 7.59/2.93  Inference rules
% 7.59/2.93  ----------------------
% 7.59/2.93  #Ref     : 0
% 7.59/2.93  #Sup     : 3978
% 7.59/2.93  #Fact    : 0
% 7.59/2.93  #Define  : 0
% 7.59/2.93  #Split   : 2
% 7.59/2.93  #Chain   : 0
% 7.59/2.93  #Close   : 0
% 7.59/2.93  
% 7.59/2.93  Ordering : KBO
% 7.59/2.93  
% 7.59/2.93  Simplification rules
% 7.59/2.93  ----------------------
% 7.59/2.93  #Subsume      : 92
% 7.59/2.93  #Demod        : 3975
% 7.59/2.93  #Tautology    : 2648
% 7.59/2.93  #SimpNegUnit  : 0
% 7.59/2.93  #BackRed      : 10
% 7.59/2.93  
% 7.59/2.93  #Partial instantiations: 0
% 7.59/2.93  #Strategies tried      : 1
% 7.59/2.93  
% 7.59/2.93  Timing (in seconds)
% 7.59/2.93  ----------------------
% 7.59/2.93  Preprocessing        : 0.32
% 7.59/2.93  Parsing              : 0.17
% 7.59/2.93  CNF conversion       : 0.02
% 7.59/2.93  Main loop            : 1.81
% 7.59/2.93  Inferencing          : 0.49
% 7.59/2.93  Reduction            : 0.88
% 7.59/2.93  Demodulation         : 0.75
% 7.59/2.93  BG Simplification    : 0.06
% 7.59/2.93  Subsumption          : 0.28
% 7.59/2.93  Abstraction          : 0.10
% 7.59/2.93  MUC search           : 0.00
% 7.59/2.93  Cooper               : 0.00
% 7.59/2.93  Total                : 2.17
% 7.59/2.93  Index Insertion      : 0.00
% 7.59/2.93  Index Deletion       : 0.00
% 7.59/2.93  Index Matching       : 0.00
% 7.59/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
