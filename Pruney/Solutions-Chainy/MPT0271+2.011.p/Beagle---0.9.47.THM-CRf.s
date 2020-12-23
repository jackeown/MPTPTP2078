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
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 8.26s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 194 expanded)
%              Number of leaves         :   35 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 203 expanded)
%              Number of equality atoms :   69 ( 150 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_46,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [B_61,A_62] : k5_xboole_0(B_61,A_62) = k5_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_62] : k5_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_772,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_871,plain,(
    ! [A_15,C_104] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_772])).

tff(c_887,plain,(
    ! [A_105,C_106] : k5_xboole_0(A_105,k5_xboole_0(A_105,C_106)) = C_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_871])).

tff(c_964,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k5_xboole_0(B_108,A_107)) = B_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_942,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_967,plain,(
    ! [B_108,A_107] : k5_xboole_0(k5_xboole_0(B_108,A_107),B_108) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_942])).

tff(c_50,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_280,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k2_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4957,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k5_xboole_0(B_184,k2_xboole_0(A_183,B_184))) = k3_xboole_0(A_183,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_18])).

tff(c_886,plain,(
    ! [A_15,C_104] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_104)) = C_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_871])).

tff(c_5004,plain,(
    ! [B_184,A_183] : k5_xboole_0(B_184,k2_xboole_0(A_183,B_184)) = k5_xboole_0(A_183,k3_xboole_0(A_183,B_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4957,c_886])).

tff(c_5141,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,k2_xboole_0(A_186,B_185)) = k4_xboole_0(A_186,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5004])).

tff(c_6134,plain,(
    ! [B_198,A_199] : k5_xboole_0(B_198,k4_xboole_0(A_199,B_198)) = k2_xboole_0(A_199,B_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_5141,c_886])).

tff(c_6237,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_6134])).

tff(c_6259,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6237])).

tff(c_20,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_301,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_368,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_301])).

tff(c_40,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_374,plain,(
    ! [B_85,A_84] : k2_xboole_0(B_85,A_84) = k2_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_40])).

tff(c_6282,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6259,c_374])).

tff(c_6317,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6282,c_18])).

tff(c_6328,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_6317])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6422,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6328,c_10])).

tff(c_36,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | ~ r1_tarski(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6434,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6422,c_36])).

tff(c_6441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_6434])).

tff(c_6442,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6463,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(k1_tarski(A_202),B_203)
      | ~ r2_hidden(A_202,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6467,plain,(
    ! [A_202,B_203] :
      ( k2_xboole_0(k1_tarski(A_202),B_203) = B_203
      | ~ r2_hidden(A_202,B_203) ) ),
    inference(resolution,[status(thm)],[c_6463,c_8])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6804,plain,(
    ! [A_227,B_228] : k5_xboole_0(k5_xboole_0(A_227,B_228),k2_xboole_0(A_227,B_228)) = k3_xboole_0(A_227,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12108,plain,(
    ! [A_318,B_319] : k5_xboole_0(A_318,k5_xboole_0(B_319,k2_xboole_0(A_318,B_319))) = k3_xboole_0(A_318,B_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6804])).

tff(c_6726,plain,(
    ! [A_224,B_225,C_226] : k5_xboole_0(k5_xboole_0(A_224,B_225),C_226) = k5_xboole_0(A_224,k5_xboole_0(B_225,C_226)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6790,plain,(
    ! [A_15,C_226] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_226)) = k5_xboole_0(k1_xboole_0,C_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6726])).

tff(c_6803,plain,(
    ! [A_15,C_226] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_226)) = C_226 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6790])).

tff(c_12161,plain,(
    ! [B_319,A_318] : k5_xboole_0(B_319,k2_xboole_0(A_318,B_319)) = k5_xboole_0(A_318,k3_xboole_0(A_318,B_319)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12108,c_6803])).

tff(c_12300,plain,(
    ! [B_320,A_321] : k5_xboole_0(B_320,k2_xboole_0(A_321,B_320)) = k4_xboole_0(A_321,B_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12161])).

tff(c_12419,plain,(
    ! [B_203,A_202] :
      ( k5_xboole_0(B_203,B_203) = k4_xboole_0(k1_tarski(A_202),B_203)
      | ~ r2_hidden(A_202,B_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6467,c_12300])).

tff(c_13214,plain,(
    ! [A_332,B_333] :
      ( k4_xboole_0(k1_tarski(A_332),B_333) = k1_xboole_0
      | ~ r2_hidden(A_332,B_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12419])).

tff(c_6443,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6616,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6443,c_48])).

tff(c_13246,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13214,c_6616])).

tff(c_13280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6442,c_13246])).

tff(c_13281,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_38,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13371,plain,(
    ! [A_346,B_347] :
      ( k2_xboole_0(A_346,B_347) = B_347
      | ~ r1_tarski(A_346,B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13381,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(k1_tarski(A_48),B_49) = B_49
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_38,c_13371])).

tff(c_14024,plain,(
    ! [A_376,B_377] : k5_xboole_0(k5_xboole_0(A_376,B_377),k2_xboole_0(A_376,B_377)) = k3_xboole_0(A_376,B_377) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18717,plain,(
    ! [A_461,B_462] : k5_xboole_0(A_461,k5_xboole_0(B_462,k2_xboole_0(A_461,B_462))) = k3_xboole_0(A_461,B_462) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_14])).

tff(c_13591,plain,(
    ! [A_365,B_366,C_367] : k5_xboole_0(k5_xboole_0(A_365,B_366),C_367) = k5_xboole_0(A_365,k5_xboole_0(B_366,C_367)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13655,plain,(
    ! [A_15,C_367] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_367)) = k5_xboole_0(k1_xboole_0,C_367) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13591])).

tff(c_13668,plain,(
    ! [A_15,C_367] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_367)) = C_367 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_13655])).

tff(c_18763,plain,(
    ! [B_462,A_461] : k5_xboole_0(B_462,k2_xboole_0(A_461,B_462)) = k5_xboole_0(A_461,k3_xboole_0(A_461,B_462)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18717,c_13668])).

tff(c_18890,plain,(
    ! [B_463,A_464] : k5_xboole_0(B_463,k2_xboole_0(A_464,B_463)) = k4_xboole_0(A_464,B_463) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18763])).

tff(c_18995,plain,(
    ! [B_49,A_48] :
      ( k5_xboole_0(B_49,B_49) = k4_xboole_0(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13381,c_18890])).

tff(c_19509,plain,(
    ! [A_471,B_472] :
      ( k4_xboole_0(k1_tarski(A_471),B_472) = k1_xboole_0
      | ~ r2_hidden(A_471,B_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18995])).

tff(c_13282,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_13342,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13282,c_44])).

tff(c_19546,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19509,c_13342])).

tff(c_19579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_19546])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.26/3.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.35  
% 8.26/3.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.35  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.26/3.35  
% 8.26/3.35  %Foreground sorts:
% 8.26/3.35  
% 8.26/3.35  
% 8.26/3.35  %Background operators:
% 8.26/3.35  
% 8.26/3.35  
% 8.26/3.35  %Foreground operators:
% 8.26/3.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.26/3.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.26/3.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.26/3.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.26/3.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.26/3.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.26/3.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.26/3.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.26/3.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.26/3.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.26/3.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.26/3.35  tff('#skF_2', type, '#skF_2': $i).
% 8.26/3.35  tff('#skF_3', type, '#skF_3': $i).
% 8.26/3.35  tff('#skF_1', type, '#skF_1': $i).
% 8.26/3.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.26/3.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.26/3.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.26/3.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.26/3.35  tff('#skF_4', type, '#skF_4': $i).
% 8.26/3.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.26/3.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.26/3.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.26/3.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.26/3.35  
% 8.26/3.37  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 8.26/3.37  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.26/3.37  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.26/3.37  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.26/3.37  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.26/3.37  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.26/3.37  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.26/3.37  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.26/3.37  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.26/3.37  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.26/3.37  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.26/3.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.26/3.37  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.37  tff(c_203, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 8.26/3.37  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/3.37  tff(c_109, plain, (![B_61, A_62]: (k5_xboole_0(B_61, A_62)=k5_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/3.37  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.26/3.37  tff(c_125, plain, (![A_62]: (k5_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 8.26/3.37  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.26/3.37  tff(c_772, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.37  tff(c_871, plain, (![A_15, C_104]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_16, c_772])).
% 8.26/3.37  tff(c_887, plain, (![A_105, C_106]: (k5_xboole_0(A_105, k5_xboole_0(A_105, C_106))=C_106)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_871])).
% 8.26/3.37  tff(c_964, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k5_xboole_0(B_108, A_107))=B_108)), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 8.26/3.37  tff(c_942, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 8.26/3.37  tff(c_967, plain, (![B_108, A_107]: (k5_xboole_0(k5_xboole_0(B_108, A_107), B_108)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_964, c_942])).
% 8.26/3.37  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.37  tff(c_280, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 8.26/3.37  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.26/3.37  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k2_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/3.37  tff(c_4957, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k5_xboole_0(B_184, k2_xboole_0(A_183, B_184)))=k3_xboole_0(A_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_772, c_18])).
% 8.26/3.37  tff(c_886, plain, (![A_15, C_104]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_104))=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_871])).
% 8.26/3.37  tff(c_5004, plain, (![B_184, A_183]: (k5_xboole_0(B_184, k2_xboole_0(A_183, B_184))=k5_xboole_0(A_183, k3_xboole_0(A_183, B_184)))), inference(superposition, [status(thm), theory('equality')], [c_4957, c_886])).
% 8.26/3.37  tff(c_5141, plain, (![B_185, A_186]: (k5_xboole_0(B_185, k2_xboole_0(A_186, B_185))=k4_xboole_0(A_186, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5004])).
% 8.26/3.37  tff(c_6134, plain, (![B_198, A_199]: (k5_xboole_0(B_198, k4_xboole_0(A_199, B_198))=k2_xboole_0(A_199, B_198))), inference(superposition, [status(thm), theory('equality')], [c_5141, c_886])).
% 8.26/3.37  tff(c_6237, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_280, c_6134])).
% 8.26/3.37  tff(c_6259, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6237])).
% 8.26/3.37  tff(c_20, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.26/3.37  tff(c_301, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.26/3.37  tff(c_368, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_20, c_301])).
% 8.26/3.37  tff(c_40, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.26/3.37  tff(c_374, plain, (![B_85, A_84]: (k2_xboole_0(B_85, A_84)=k2_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_368, c_40])).
% 8.26/3.37  tff(c_6282, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6259, c_374])).
% 8.26/3.37  tff(c_6317, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6282, c_18])).
% 8.26/3.37  tff(c_6328, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_6317])).
% 8.26/3.37  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.26/3.37  tff(c_6422, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6328, c_10])).
% 8.26/3.37  tff(c_36, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | ~r1_tarski(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.37  tff(c_6434, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6422, c_36])).
% 8.26/3.37  tff(c_6441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_6434])).
% 8.26/3.37  tff(c_6442, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 8.26/3.37  tff(c_6463, plain, (![A_202, B_203]: (r1_tarski(k1_tarski(A_202), B_203) | ~r2_hidden(A_202, B_203))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.37  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.26/3.37  tff(c_6467, plain, (![A_202, B_203]: (k2_xboole_0(k1_tarski(A_202), B_203)=B_203 | ~r2_hidden(A_202, B_203))), inference(resolution, [status(thm)], [c_6463, c_8])).
% 8.26/3.37  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.37  tff(c_6804, plain, (![A_227, B_228]: (k5_xboole_0(k5_xboole_0(A_227, B_228), k2_xboole_0(A_227, B_228))=k3_xboole_0(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/3.37  tff(c_12108, plain, (![A_318, B_319]: (k5_xboole_0(A_318, k5_xboole_0(B_319, k2_xboole_0(A_318, B_319)))=k3_xboole_0(A_318, B_319))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6804])).
% 8.26/3.37  tff(c_6726, plain, (![A_224, B_225, C_226]: (k5_xboole_0(k5_xboole_0(A_224, B_225), C_226)=k5_xboole_0(A_224, k5_xboole_0(B_225, C_226)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.37  tff(c_6790, plain, (![A_15, C_226]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_226))=k5_xboole_0(k1_xboole_0, C_226))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6726])).
% 8.26/3.37  tff(c_6803, plain, (![A_15, C_226]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_226))=C_226)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_6790])).
% 8.26/3.37  tff(c_12161, plain, (![B_319, A_318]: (k5_xboole_0(B_319, k2_xboole_0(A_318, B_319))=k5_xboole_0(A_318, k3_xboole_0(A_318, B_319)))), inference(superposition, [status(thm), theory('equality')], [c_12108, c_6803])).
% 8.26/3.37  tff(c_12300, plain, (![B_320, A_321]: (k5_xboole_0(B_320, k2_xboole_0(A_321, B_320))=k4_xboole_0(A_321, B_320))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12161])).
% 8.26/3.37  tff(c_12419, plain, (![B_203, A_202]: (k5_xboole_0(B_203, B_203)=k4_xboole_0(k1_tarski(A_202), B_203) | ~r2_hidden(A_202, B_203))), inference(superposition, [status(thm), theory('equality')], [c_6467, c_12300])).
% 8.26/3.37  tff(c_13214, plain, (![A_332, B_333]: (k4_xboole_0(k1_tarski(A_332), B_333)=k1_xboole_0 | ~r2_hidden(A_332, B_333))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12419])).
% 8.26/3.37  tff(c_6443, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 8.26/3.37  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.37  tff(c_6616, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6443, c_48])).
% 8.26/3.37  tff(c_13246, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13214, c_6616])).
% 8.26/3.37  tff(c_13280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6442, c_13246])).
% 8.26/3.37  tff(c_13281, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 8.26/3.37  tff(c_38, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.37  tff(c_13371, plain, (![A_346, B_347]: (k2_xboole_0(A_346, B_347)=B_347 | ~r1_tarski(A_346, B_347))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.26/3.37  tff(c_13381, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)=B_49 | ~r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_38, c_13371])).
% 8.26/3.37  tff(c_14024, plain, (![A_376, B_377]: (k5_xboole_0(k5_xboole_0(A_376, B_377), k2_xboole_0(A_376, B_377))=k3_xboole_0(A_376, B_377))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/3.37  tff(c_18717, plain, (![A_461, B_462]: (k5_xboole_0(A_461, k5_xboole_0(B_462, k2_xboole_0(A_461, B_462)))=k3_xboole_0(A_461, B_462))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_14])).
% 8.26/3.37  tff(c_13591, plain, (![A_365, B_366, C_367]: (k5_xboole_0(k5_xboole_0(A_365, B_366), C_367)=k5_xboole_0(A_365, k5_xboole_0(B_366, C_367)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.26/3.37  tff(c_13655, plain, (![A_15, C_367]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_367))=k5_xboole_0(k1_xboole_0, C_367))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13591])).
% 8.26/3.37  tff(c_13668, plain, (![A_15, C_367]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_367))=C_367)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_13655])).
% 8.26/3.37  tff(c_18763, plain, (![B_462, A_461]: (k5_xboole_0(B_462, k2_xboole_0(A_461, B_462))=k5_xboole_0(A_461, k3_xboole_0(A_461, B_462)))), inference(superposition, [status(thm), theory('equality')], [c_18717, c_13668])).
% 8.26/3.37  tff(c_18890, plain, (![B_463, A_464]: (k5_xboole_0(B_463, k2_xboole_0(A_464, B_463))=k4_xboole_0(A_464, B_463))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18763])).
% 8.26/3.37  tff(c_18995, plain, (![B_49, A_48]: (k5_xboole_0(B_49, B_49)=k4_xboole_0(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_13381, c_18890])).
% 8.26/3.37  tff(c_19509, plain, (![A_471, B_472]: (k4_xboole_0(k1_tarski(A_471), B_472)=k1_xboole_0 | ~r2_hidden(A_471, B_472))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18995])).
% 8.26/3.37  tff(c_13282, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 8.26/3.37  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/3.37  tff(c_13342, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13282, c_44])).
% 8.26/3.37  tff(c_19546, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19509, c_13342])).
% 8.26/3.37  tff(c_19579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13281, c_19546])).
% 8.26/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.37  
% 8.26/3.37  Inference rules
% 8.26/3.37  ----------------------
% 8.26/3.37  #Ref     : 0
% 8.26/3.37  #Sup     : 4867
% 8.26/3.37  #Fact    : 0
% 8.26/3.37  #Define  : 0
% 8.26/3.37  #Split   : 2
% 8.26/3.37  #Chain   : 0
% 8.26/3.37  #Close   : 0
% 8.26/3.37  
% 8.26/3.37  Ordering : KBO
% 8.26/3.37  
% 8.26/3.37  Simplification rules
% 8.26/3.37  ----------------------
% 8.26/3.37  #Subsume      : 179
% 8.26/3.37  #Demod        : 4756
% 8.26/3.37  #Tautology    : 2573
% 8.26/3.37  #SimpNegUnit  : 2
% 8.26/3.37  #BackRed      : 3
% 8.26/3.37  
% 8.26/3.37  #Partial instantiations: 0
% 8.26/3.37  #Strategies tried      : 1
% 8.26/3.37  
% 8.26/3.37  Timing (in seconds)
% 8.26/3.37  ----------------------
% 8.26/3.37  Preprocessing        : 0.33
% 8.26/3.37  Parsing              : 0.18
% 8.26/3.37  CNF conversion       : 0.02
% 8.26/3.37  Main loop            : 2.21
% 8.26/3.37  Inferencing          : 0.55
% 8.26/3.37  Reduction            : 1.17
% 8.26/3.37  Demodulation         : 1.03
% 8.26/3.37  BG Simplification    : 0.08
% 8.26/3.37  Subsumption          : 0.29
% 8.26/3.37  Abstraction          : 0.11
% 8.26/3.37  MUC search           : 0.00
% 8.26/3.37  Cooper               : 0.00
% 8.26/3.37  Total                : 2.57
% 8.26/3.37  Index Insertion      : 0.00
% 8.26/3.37  Index Deletion       : 0.00
% 8.26/3.37  Index Matching       : 0.00
% 8.26/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
