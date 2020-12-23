%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:04 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 193 expanded)
%              Number of leaves         :   43 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 209 expanded)
%              Number of equality atoms :   71 ( 144 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_94,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_80,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_186,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_48,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_66] : k3_tarski(k1_tarski(A_66)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_246,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_255,plain,(
    ! [A_34] : k3_tarski(k1_tarski(A_34)) = k2_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_246])).

tff(c_258,plain,(
    ! [A_34] : k2_xboole_0(A_34,A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_255])).

tff(c_139,plain,(
    ! [B_77,A_78] : k5_xboole_0(B_77,A_78) = k5_xboole_0(A_78,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    ! [A_78] : k5_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_34])).

tff(c_1099,plain,(
    ! [A_140,B_141] : k5_xboole_0(k5_xboole_0(A_140,B_141),k2_xboole_0(A_140,B_141)) = k3_xboole_0(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1199,plain,(
    ! [A_24] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_24,A_24)) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1099])).

tff(c_1210,plain,(
    ! [A_142] : k3_xboole_0(A_142,A_142) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_155,c_1199])).

tff(c_28,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1224,plain,(
    ! [A_142] : k5_xboole_0(A_142,A_142) = k4_xboole_0(A_142,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_28])).

tff(c_1232,plain,(
    ! [A_143] : k4_xboole_0(A_143,A_143) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1224])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1271,plain,(
    ! [D_147,A_148] :
      ( ~ r2_hidden(D_147,A_148)
      | ~ r2_hidden(D_147,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_6])).

tff(c_1274,plain,(
    ! [C_33] : ~ r2_hidden(C_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_1271])).

tff(c_84,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_282,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1470,plain,(
    ! [D_161,A_162,B_163] :
      ( r2_hidden(D_161,k4_xboole_0(A_162,B_163))
      | r2_hidden(D_161,B_163)
      | ~ r2_hidden(D_161,A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1491,plain,(
    ! [D_161] :
      ( r2_hidden(D_161,k1_xboole_0)
      | r2_hidden(D_161,'#skF_8')
      | ~ r2_hidden(D_161,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_1470])).

tff(c_1499,plain,(
    ! [D_164] :
      ( r2_hidden(D_164,'#skF_8')
      | ~ r2_hidden(D_164,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1274,c_1491])).

tff(c_1503,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1499])).

tff(c_1507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_1503])).

tff(c_1508,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_72,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1777,plain,(
    ! [A_192,B_193,C_194] : k5_xboole_0(k5_xboole_0(A_192,B_193),C_194) = k5_xboole_0(A_192,k5_xboole_0(B_193,C_194)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1863,plain,(
    ! [A_24,C_194] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_194)) = k5_xboole_0(k1_xboole_0,C_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1777])).

tff(c_1878,plain,(
    ! [A_195,C_196] : k5_xboole_0(A_195,k5_xboole_0(A_195,C_196)) = C_196 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1863])).

tff(c_1927,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1878])).

tff(c_36,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_272,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(A_85,B_86) = B_86
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_279,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(resolution,[status(thm)],[c_36,c_272])).

tff(c_2136,plain,(
    ! [A_201,B_202] : k5_xboole_0(k5_xboole_0(A_201,B_202),k2_xboole_0(A_201,B_202)) = k3_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6782,plain,(
    ! [A_7012,B_7013] : k5_xboole_0(k2_xboole_0(A_7012,B_7013),k5_xboole_0(A_7012,B_7013)) = k3_xboole_0(A_7012,B_7013) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2136])).

tff(c_6869,plain,(
    ! [A_19,B_20] : k5_xboole_0(k2_xboole_0(A_19,B_20),k5_xboole_0(A_19,k2_xboole_0(A_19,B_20))) = k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_6782])).

tff(c_6910,plain,(
    ! [A_7069,B_7070] : k3_xboole_0(A_7069,k2_xboole_0(A_7069,B_7070)) = A_7069 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_6869])).

tff(c_6926,plain,(
    ! [A_7069,B_7070] : k4_xboole_0(A_7069,k2_xboole_0(A_7069,B_7070)) = k5_xboole_0(A_7069,A_7069) ),
    inference(superposition,[status(thm),theory(equality)],[c_6910,c_28])).

tff(c_6961,plain,(
    ! [A_7126,B_7127] : k4_xboole_0(A_7126,k2_xboole_0(A_7126,B_7127)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6926])).

tff(c_7038,plain,(
    ! [A_7183,B_7184] :
      ( k4_xboole_0(k1_tarski(A_7183),B_7184) = k1_xboole_0
      | ~ r2_hidden(A_7183,B_7184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6961])).

tff(c_1509,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1631,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1509,c_82])).

tff(c_7091,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7038,c_1631])).

tff(c_7195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_7091])).

tff(c_7196,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_44,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7678,plain,(
    ! [A_7286,B_7287,C_7288] : k5_xboole_0(k5_xboole_0(A_7286,B_7287),C_7288) = k5_xboole_0(A_7286,k5_xboole_0(B_7287,C_7288)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7777,plain,(
    ! [A_24,C_7288] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_7288)) = k5_xboole_0(k1_xboole_0,C_7288) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7678])).

tff(c_7793,plain,(
    ! [A_7289,C_7290] : k5_xboole_0(A_7289,k5_xboole_0(A_7289,C_7290)) = C_7290 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_7777])).

tff(c_8984,plain,(
    ! [A_10620,B_10621] : k5_xboole_0(A_10620,k2_xboole_0(A_10620,B_10621)) = k4_xboole_0(B_10621,A_10620) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7793])).

tff(c_7848,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7793])).

tff(c_9004,plain,(
    ! [A_10620,B_10621] : k5_xboole_0(k2_xboole_0(A_10620,B_10621),k4_xboole_0(B_10621,A_10620)) = A_10620 ),
    inference(superposition,[status(thm),theory(equality)],[c_8984,c_7848])).

tff(c_7285,plain,(
    ! [A_7246,B_7247] :
      ( k2_xboole_0(A_7246,B_7247) = B_7247
      | ~ r1_tarski(A_7246,B_7247) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7292,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(resolution,[status(thm)],[c_36,c_7285])).

tff(c_7835,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k4_xboole_0(B_28,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7793])).

tff(c_7554,plain,(
    ! [A_7282,B_7283] : k5_xboole_0(k5_xboole_0(A_7282,B_7283),k2_xboole_0(A_7282,B_7283)) = k3_xboole_0(A_7282,B_7283) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12232,plain,(
    ! [A_14759,B_14760] : k5_xboole_0(k2_xboole_0(A_14759,B_14760),k5_xboole_0(A_14759,B_14760)) = k3_xboole_0(A_14759,B_14760) ),
    inference(superposition,[status(thm),theory(equality)],[c_7554,c_2])).

tff(c_12283,plain,(
    ! [A_27,B_28] : k5_xboole_0(k2_xboole_0(A_27,k2_xboole_0(A_27,B_28)),k4_xboole_0(B_28,A_27)) = k3_xboole_0(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7835,c_12232])).

tff(c_12350,plain,(
    ! [A_14816,B_14817] : k3_xboole_0(A_14816,k2_xboole_0(A_14816,B_14817)) = A_14816 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9004,c_7292,c_12283])).

tff(c_12366,plain,(
    ! [A_14816,B_14817] : k4_xboole_0(A_14816,k2_xboole_0(A_14816,B_14817)) = k5_xboole_0(A_14816,A_14816) ),
    inference(superposition,[status(thm),theory(equality)],[c_12350,c_28])).

tff(c_12401,plain,(
    ! [A_14873,B_14874] : k4_xboole_0(A_14873,k2_xboole_0(A_14873,B_14874)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12366])).

tff(c_15192,plain,(
    ! [A_15955,B_15956] :
      ( k4_xboole_0(k1_tarski(A_15955),B_15956) = k1_xboole_0
      | ~ r2_hidden(A_15955,B_15956) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_12401])).

tff(c_7197,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_78,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7271,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7197,c_78])).

tff(c_15253,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15192,c_7271])).

tff(c_15350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7196,c_15253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.87/2.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/2.84  
% 7.87/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/2.84  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 7.87/2.84  
% 7.87/2.84  %Foreground sorts:
% 7.87/2.84  
% 7.87/2.84  
% 7.87/2.84  %Background operators:
% 7.87/2.84  
% 7.87/2.84  
% 7.87/2.84  %Foreground operators:
% 7.87/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.87/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.87/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.87/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.87/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.87/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.87/2.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.87/2.84  tff('#skF_7', type, '#skF_7': $i).
% 7.87/2.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.87/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.87/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.87/2.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.87/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.87/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.87/2.84  tff('#skF_6', type, '#skF_6': $i).
% 7.87/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.87/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.87/2.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.87/2.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.87/2.84  tff('#skF_8', type, '#skF_8': $i).
% 7.87/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.87/2.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.87/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.87/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.87/2.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.87/2.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.87/2.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.87/2.84  
% 7.87/2.86  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 7.87/2.86  tff(f_72, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.87/2.86  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.87/2.86  tff(f_94, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 7.87/2.86  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.87/2.86  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.87/2.86  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.87/2.86  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.87/2.86  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.87/2.86  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.87/2.86  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.87/2.86  tff(f_90, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 7.87/2.86  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.87/2.86  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.87/2.86  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.87/2.86  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.87/2.86  tff(c_80, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.86  tff(c_186, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_80])).
% 7.87/2.86  tff(c_48, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.87/2.86  tff(c_40, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.87/2.86  tff(c_76, plain, (![A_66]: (k3_tarski(k1_tarski(A_66))=A_66)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.87/2.86  tff(c_58, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.86  tff(c_246, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.87/2.86  tff(c_255, plain, (![A_34]: (k3_tarski(k1_tarski(A_34))=k2_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_58, c_246])).
% 7.87/2.86  tff(c_258, plain, (![A_34]: (k2_xboole_0(A_34, A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_255])).
% 7.87/2.86  tff(c_139, plain, (![B_77, A_78]: (k5_xboole_0(B_77, A_78)=k5_xboole_0(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.87/2.86  tff(c_34, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.87/2.86  tff(c_155, plain, (![A_78]: (k5_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_139, c_34])).
% 7.87/2.86  tff(c_1099, plain, (![A_140, B_141]: (k5_xboole_0(k5_xboole_0(A_140, B_141), k2_xboole_0(A_140, B_141))=k3_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.87/2.86  tff(c_1199, plain, (![A_24]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_24, A_24))=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1099])).
% 7.87/2.86  tff(c_1210, plain, (![A_142]: (k3_xboole_0(A_142, A_142)=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_155, c_1199])).
% 7.87/2.86  tff(c_28, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.87/2.86  tff(c_1224, plain, (![A_142]: (k5_xboole_0(A_142, A_142)=k4_xboole_0(A_142, A_142))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_28])).
% 7.87/2.86  tff(c_1232, plain, (![A_143]: (k4_xboole_0(A_143, A_143)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1224])).
% 7.87/2.86  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.87/2.86  tff(c_1271, plain, (![D_147, A_148]: (~r2_hidden(D_147, A_148) | ~r2_hidden(D_147, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_6])).
% 7.87/2.86  tff(c_1274, plain, (![C_33]: (~r2_hidden(C_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_1271])).
% 7.87/2.86  tff(c_84, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.86  tff(c_282, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_84])).
% 7.87/2.86  tff(c_1470, plain, (![D_161, A_162, B_163]: (r2_hidden(D_161, k4_xboole_0(A_162, B_163)) | r2_hidden(D_161, B_163) | ~r2_hidden(D_161, A_162))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.87/2.86  tff(c_1491, plain, (![D_161]: (r2_hidden(D_161, k1_xboole_0) | r2_hidden(D_161, '#skF_8') | ~r2_hidden(D_161, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_282, c_1470])).
% 7.87/2.86  tff(c_1499, plain, (![D_164]: (r2_hidden(D_164, '#skF_8') | ~r2_hidden(D_164, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_1274, c_1491])).
% 7.87/2.86  tff(c_1503, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_1499])).
% 7.87/2.86  tff(c_1507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_1503])).
% 7.87/2.86  tff(c_1508, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 7.87/2.86  tff(c_72, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.87/2.86  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.87/2.86  tff(c_1777, plain, (![A_192, B_193, C_194]: (k5_xboole_0(k5_xboole_0(A_192, B_193), C_194)=k5_xboole_0(A_192, k5_xboole_0(B_193, C_194)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.87/2.86  tff(c_1863, plain, (![A_24, C_194]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_194))=k5_xboole_0(k1_xboole_0, C_194))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1777])).
% 7.87/2.86  tff(c_1878, plain, (![A_195, C_196]: (k5_xboole_0(A_195, k5_xboole_0(A_195, C_196))=C_196)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1863])).
% 7.87/2.86  tff(c_1927, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1878])).
% 7.87/2.86  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.87/2.86  tff(c_272, plain, (![A_85, B_86]: (k2_xboole_0(A_85, B_86)=B_86 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.87/2.86  tff(c_279, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_36, c_272])).
% 7.87/2.86  tff(c_2136, plain, (![A_201, B_202]: (k5_xboole_0(k5_xboole_0(A_201, B_202), k2_xboole_0(A_201, B_202))=k3_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.87/2.86  tff(c_6782, plain, (![A_7012, B_7013]: (k5_xboole_0(k2_xboole_0(A_7012, B_7013), k5_xboole_0(A_7012, B_7013))=k3_xboole_0(A_7012, B_7013))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2136])).
% 7.87/2.86  tff(c_6869, plain, (![A_19, B_20]: (k5_xboole_0(k2_xboole_0(A_19, B_20), k5_xboole_0(A_19, k2_xboole_0(A_19, B_20)))=k3_xboole_0(A_19, k2_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_6782])).
% 7.87/2.86  tff(c_6910, plain, (![A_7069, B_7070]: (k3_xboole_0(A_7069, k2_xboole_0(A_7069, B_7070))=A_7069)), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_6869])).
% 7.87/2.86  tff(c_6926, plain, (![A_7069, B_7070]: (k4_xboole_0(A_7069, k2_xboole_0(A_7069, B_7070))=k5_xboole_0(A_7069, A_7069))), inference(superposition, [status(thm), theory('equality')], [c_6910, c_28])).
% 7.87/2.86  tff(c_6961, plain, (![A_7126, B_7127]: (k4_xboole_0(A_7126, k2_xboole_0(A_7126, B_7127))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6926])).
% 7.87/2.86  tff(c_7038, plain, (![A_7183, B_7184]: (k4_xboole_0(k1_tarski(A_7183), B_7184)=k1_xboole_0 | ~r2_hidden(A_7183, B_7184))), inference(superposition, [status(thm), theory('equality')], [c_72, c_6961])).
% 7.87/2.86  tff(c_1509, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_84])).
% 7.87/2.86  tff(c_82, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.86  tff(c_1631, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1509, c_82])).
% 7.87/2.86  tff(c_7091, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7038, c_1631])).
% 7.87/2.86  tff(c_7195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1508, c_7091])).
% 7.87/2.86  tff(c_7196, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 7.87/2.86  tff(c_44, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.87/2.86  tff(c_7678, plain, (![A_7286, B_7287, C_7288]: (k5_xboole_0(k5_xboole_0(A_7286, B_7287), C_7288)=k5_xboole_0(A_7286, k5_xboole_0(B_7287, C_7288)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.87/2.86  tff(c_7777, plain, (![A_24, C_7288]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_7288))=k5_xboole_0(k1_xboole_0, C_7288))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7678])).
% 7.87/2.86  tff(c_7793, plain, (![A_7289, C_7290]: (k5_xboole_0(A_7289, k5_xboole_0(A_7289, C_7290))=C_7290)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_7777])).
% 7.87/2.86  tff(c_8984, plain, (![A_10620, B_10621]: (k5_xboole_0(A_10620, k2_xboole_0(A_10620, B_10621))=k4_xboole_0(B_10621, A_10620))), inference(superposition, [status(thm), theory('equality')], [c_44, c_7793])).
% 7.87/2.86  tff(c_7848, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_7793])).
% 7.87/2.86  tff(c_9004, plain, (![A_10620, B_10621]: (k5_xboole_0(k2_xboole_0(A_10620, B_10621), k4_xboole_0(B_10621, A_10620))=A_10620)), inference(superposition, [status(thm), theory('equality')], [c_8984, c_7848])).
% 7.87/2.86  tff(c_7285, plain, (![A_7246, B_7247]: (k2_xboole_0(A_7246, B_7247)=B_7247 | ~r1_tarski(A_7246, B_7247))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.87/2.86  tff(c_7292, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_36, c_7285])).
% 7.87/2.86  tff(c_7835, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k4_xboole_0(B_28, A_27))), inference(superposition, [status(thm), theory('equality')], [c_44, c_7793])).
% 7.87/2.86  tff(c_7554, plain, (![A_7282, B_7283]: (k5_xboole_0(k5_xboole_0(A_7282, B_7283), k2_xboole_0(A_7282, B_7283))=k3_xboole_0(A_7282, B_7283))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.87/2.86  tff(c_12232, plain, (![A_14759, B_14760]: (k5_xboole_0(k2_xboole_0(A_14759, B_14760), k5_xboole_0(A_14759, B_14760))=k3_xboole_0(A_14759, B_14760))), inference(superposition, [status(thm), theory('equality')], [c_7554, c_2])).
% 7.87/2.86  tff(c_12283, plain, (![A_27, B_28]: (k5_xboole_0(k2_xboole_0(A_27, k2_xboole_0(A_27, B_28)), k4_xboole_0(B_28, A_27))=k3_xboole_0(A_27, k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_7835, c_12232])).
% 7.87/2.86  tff(c_12350, plain, (![A_14816, B_14817]: (k3_xboole_0(A_14816, k2_xboole_0(A_14816, B_14817))=A_14816)), inference(demodulation, [status(thm), theory('equality')], [c_9004, c_7292, c_12283])).
% 7.87/2.86  tff(c_12366, plain, (![A_14816, B_14817]: (k4_xboole_0(A_14816, k2_xboole_0(A_14816, B_14817))=k5_xboole_0(A_14816, A_14816))), inference(superposition, [status(thm), theory('equality')], [c_12350, c_28])).
% 7.87/2.86  tff(c_12401, plain, (![A_14873, B_14874]: (k4_xboole_0(A_14873, k2_xboole_0(A_14873, B_14874))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12366])).
% 7.87/2.86  tff(c_15192, plain, (![A_15955, B_15956]: (k4_xboole_0(k1_tarski(A_15955), B_15956)=k1_xboole_0 | ~r2_hidden(A_15955, B_15956))), inference(superposition, [status(thm), theory('equality')], [c_72, c_12401])).
% 7.87/2.86  tff(c_7197, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_80])).
% 7.87/2.86  tff(c_78, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.86  tff(c_7271, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7197, c_78])).
% 7.87/2.86  tff(c_15253, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15192, c_7271])).
% 7.87/2.86  tff(c_15350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7196, c_15253])).
% 7.87/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/2.86  
% 7.87/2.86  Inference rules
% 7.87/2.86  ----------------------
% 7.87/2.86  #Ref     : 0
% 7.87/2.86  #Sup     : 3387
% 7.87/2.86  #Fact    : 0
% 7.87/2.86  #Define  : 0
% 7.87/2.86  #Split   : 9
% 7.87/2.86  #Chain   : 0
% 7.87/2.86  #Close   : 0
% 7.87/2.86  
% 7.87/2.86  Ordering : KBO
% 7.87/2.86  
% 7.87/2.86  Simplification rules
% 7.87/2.86  ----------------------
% 7.87/2.86  #Subsume      : 289
% 7.87/2.86  #Demod        : 2830
% 7.87/2.86  #Tautology    : 1951
% 7.87/2.86  #SimpNegUnit  : 53
% 7.87/2.86  #BackRed      : 60
% 7.87/2.86  
% 7.87/2.86  #Partial instantiations: 6138
% 7.87/2.86  #Strategies tried      : 1
% 7.87/2.86  
% 7.87/2.86  Timing (in seconds)
% 7.87/2.86  ----------------------
% 7.87/2.86  Preprocessing        : 0.35
% 7.87/2.86  Parsing              : 0.19
% 7.87/2.86  CNF conversion       : 0.03
% 7.87/2.86  Main loop            : 1.73
% 7.87/2.86  Inferencing          : 0.64
% 7.87/2.86  Reduction            : 0.68
% 7.87/2.86  Demodulation         : 0.56
% 7.87/2.86  BG Simplification    : 0.06
% 7.87/2.86  Subsumption          : 0.24
% 7.87/2.86  Abstraction          : 0.09
% 7.87/2.86  MUC search           : 0.00
% 7.87/2.86  Cooper               : 0.00
% 7.87/2.86  Total                : 2.11
% 7.87/2.86  Index Insertion      : 0.00
% 7.87/2.86  Index Deletion       : 0.00
% 7.87/2.86  Index Matching       : 0.00
% 7.87/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
