%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 8.92s
% Output     : CNFRefutation 9.03s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 442 expanded)
%              Number of leaves         :   28 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :   65 ( 434 expanded)
%              Number of equality atoms :   54 ( 419 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [C_44,A_42,B_43] :
      ( k4_xboole_0(C_44,k2_tarski(A_42,B_43)) = C_44
      | r2_hidden(B_43,C_44)
      | r2_hidden(A_42,C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k5_xboole_0(k5_xboole_0(A_7,B_8),C_9) = k5_xboole_0(A_7,k5_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_340,plain,(
    ! [A_71,B_72] : k5_xboole_0(k5_xboole_0(A_71,B_72),k2_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2437,plain,(
    ! [A_125,B_126] : k5_xboole_0(A_125,k5_xboole_0(B_126,k2_xboole_0(A_125,B_126))) = k3_xboole_0(A_125,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_340])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,(
    ! [A_65,B_66,C_67] : k5_xboole_0(k5_xboole_0(A_65,B_66),C_67) = k5_xboole_0(A_65,k5_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_247,plain,(
    ! [A_10,C_67] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_67)) = k5_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_2470,plain,(
    ! [B_126,A_125] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_126,k2_xboole_0(A_125,B_126))) = k5_xboole_0(A_125,k3_xboole_0(A_125,B_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_247])).

tff(c_2531,plain,(
    ! [B_126,A_125] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_126,k2_xboole_0(A_125,B_126))) = k4_xboole_0(A_125,B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2470])).

tff(c_5807,plain,(
    ! [B_170,A_171] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_170,k2_xboole_0(A_171,B_170))) = k4_xboole_0(A_171,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2470])).

tff(c_5850,plain,(
    ! [B_170,A_171] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_170,k2_xboole_0(A_171,B_170))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_171,B_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5807,c_247])).

tff(c_5940,plain,(
    ! [A_171,B_170] : k5_xboole_0(k1_xboole_0,k4_xboole_0(A_171,B_170)) = k4_xboole_0(A_171,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_5850])).

tff(c_14,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_413,plain,(
    ! [A_74,C_75] : k5_xboole_0(A_74,k5_xboole_0(A_74,C_75)) = k5_xboole_0(k1_xboole_0,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_479,plain,(
    ! [B_14,A_13] : k5_xboole_0(k1_xboole_0,k4_xboole_0(B_14,A_13)) = k5_xboole_0(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_413])).

tff(c_6064,plain,(
    ! [A_174,B_175] : k5_xboole_0(A_174,k2_xboole_0(A_174,B_175)) = k4_xboole_0(B_175,A_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_479])).

tff(c_6201,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6064])).

tff(c_75,plain,(
    ! [A_48,B_49] : k3_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_127,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_127])).

tff(c_142,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_374,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k5_xboole_0(B_8,k2_xboole_0(A_7,B_8))) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_340])).

tff(c_6968,plain,(
    ! [A_184,B_185] : k5_xboole_0(A_184,k4_xboole_0(A_184,B_185)) = k3_xboole_0(A_184,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6201,c_374])).

tff(c_7085,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_6968])).

tff(c_7114,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7085])).

tff(c_589,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,A_77) = k5_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_413])).

tff(c_604,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_77,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_247])).

tff(c_224,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k5_xboole_0(B_66,k5_xboole_0(A_65,B_66))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_10])).

tff(c_497,plain,(
    ! [C_76] : k5_xboole_0(C_76,k5_xboole_0(k1_xboole_0,C_76)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_224])).

tff(c_921,plain,(
    ! [C_89] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,C_89)) = k5_xboole_0(C_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_247])).

tff(c_985,plain,(
    ! [A_77] : k5_xboole_0(k5_xboole_0(A_77,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,A_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_921])).

tff(c_1058,plain,(
    ! [A_77] : k5_xboole_0(k5_xboole_0(A_77,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_985])).

tff(c_7122,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7114,c_7114,c_1058])).

tff(c_7710,plain,(
    ! [A_191,C_192] : k5_xboole_0(A_191,k5_xboole_0(A_191,C_192)) = C_192 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7122,c_247])).

tff(c_8939,plain,(
    ! [B_203,A_204] : k5_xboole_0(B_203,k4_xboole_0(A_204,B_203)) = k2_xboole_0(A_204,B_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_6201,c_7710])).

tff(c_9047,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),k1_xboole_0) = k2_xboole_0(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_8939])).

tff(c_10275,plain,(
    ! [A_222,B_223] : k2_xboole_0(A_222,k2_xboole_0(B_223,A_222)) = k2_xboole_0(B_223,A_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7114,c_9047])).

tff(c_6062,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k4_xboole_0(B_14,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_479])).

tff(c_10316,plain,(
    ! [A_222,B_223] : k5_xboole_0(A_222,k2_xboole_0(B_223,A_222)) = k4_xboole_0(k2_xboole_0(B_223,A_222),A_222) ),
    inference(superposition,[status(thm),theory(equality)],[c_10275,c_6062])).

tff(c_10403,plain,(
    ! [B_223,A_222] : k4_xboole_0(k2_xboole_0(B_223,A_222),A_222) = k4_xboole_0(B_223,A_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6201,c_10316])).

tff(c_30,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15268,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10403,c_30])).

tff(c_15412,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15268])).

tff(c_15416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_15412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.92/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.96/3.30  
% 8.96/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.96/3.30  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.96/3.30  
% 8.96/3.30  %Foreground sorts:
% 8.96/3.30  
% 8.96/3.30  
% 8.96/3.30  %Background operators:
% 8.96/3.30  
% 8.96/3.30  
% 8.96/3.30  %Foreground operators:
% 8.96/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.96/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.96/3.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.96/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.96/3.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.96/3.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.96/3.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.96/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.96/3.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.96/3.30  tff('#skF_2', type, '#skF_2': $i).
% 8.96/3.30  tff('#skF_3', type, '#skF_3': $i).
% 8.96/3.30  tff('#skF_1', type, '#skF_1': $i).
% 8.96/3.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.96/3.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.96/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.96/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.96/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.96/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.96/3.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.96/3.30  
% 9.03/3.32  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 9.03/3.32  tff(f_61, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 9.03/3.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.03/3.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.03/3.32  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.03/3.32  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.03/3.32  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.03/3.32  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.03/3.32  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.03/3.32  tff(c_34, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.03/3.32  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.03/3.32  tff(c_28, plain, (![C_44, A_42, B_43]: (k4_xboole_0(C_44, k2_tarski(A_42, B_43))=C_44 | r2_hidden(B_43, C_44) | r2_hidden(A_42, C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.03/3.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.03/3.32  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.03/3.32  tff(c_8, plain, (![A_7, B_8, C_9]: (k5_xboole_0(k5_xboole_0(A_7, B_8), C_9)=k5_xboole_0(A_7, k5_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.03/3.32  tff(c_340, plain, (![A_71, B_72]: (k5_xboole_0(k5_xboole_0(A_71, B_72), k2_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.03/3.32  tff(c_2437, plain, (![A_125, B_126]: (k5_xboole_0(A_125, k5_xboole_0(B_126, k2_xboole_0(A_125, B_126)))=k3_xboole_0(A_125, B_126))), inference(superposition, [status(thm), theory('equality')], [c_8, c_340])).
% 9.03/3.32  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.03/3.32  tff(c_206, plain, (![A_65, B_66, C_67]: (k5_xboole_0(k5_xboole_0(A_65, B_66), C_67)=k5_xboole_0(A_65, k5_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.03/3.32  tff(c_247, plain, (![A_10, C_67]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_67))=k5_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_10, c_206])).
% 9.03/3.32  tff(c_2470, plain, (![B_126, A_125]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_126, k2_xboole_0(A_125, B_126)))=k5_xboole_0(A_125, k3_xboole_0(A_125, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_247])).
% 9.03/3.32  tff(c_2531, plain, (![B_126, A_125]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_126, k2_xboole_0(A_125, B_126)))=k4_xboole_0(A_125, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2470])).
% 9.03/3.32  tff(c_5807, plain, (![B_170, A_171]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_170, k2_xboole_0(A_171, B_170)))=k4_xboole_0(A_171, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2470])).
% 9.03/3.32  tff(c_5850, plain, (![B_170, A_171]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_170, k2_xboole_0(A_171, B_170)))=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_171, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_5807, c_247])).
% 9.03/3.32  tff(c_5940, plain, (![A_171, B_170]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(A_171, B_170))=k4_xboole_0(A_171, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_5850])).
% 9.03/3.32  tff(c_14, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.03/3.32  tff(c_413, plain, (![A_74, C_75]: (k5_xboole_0(A_74, k5_xboole_0(A_74, C_75))=k5_xboole_0(k1_xboole_0, C_75))), inference(superposition, [status(thm), theory('equality')], [c_10, c_206])).
% 9.03/3.32  tff(c_479, plain, (![B_14, A_13]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(B_14, A_13))=k5_xboole_0(A_13, k2_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_413])).
% 9.03/3.32  tff(c_6064, plain, (![A_174, B_175]: (k5_xboole_0(A_174, k2_xboole_0(A_174, B_175))=k4_xboole_0(B_175, A_174))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_479])).
% 9.03/3.32  tff(c_6201, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6064])).
% 9.03/3.32  tff(c_75, plain, (![A_48, B_49]: (k3_xboole_0(A_48, k2_xboole_0(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.03/3.32  tff(c_84, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 9.03/3.32  tff(c_127, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.03/3.32  tff(c_136, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k5_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_84, c_127])).
% 9.03/3.32  tff(c_142, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 9.03/3.32  tff(c_374, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k5_xboole_0(B_8, k2_xboole_0(A_7, B_8)))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_340])).
% 9.03/3.32  tff(c_6968, plain, (![A_184, B_185]: (k5_xboole_0(A_184, k4_xboole_0(A_184, B_185))=k3_xboole_0(A_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_6201, c_374])).
% 9.03/3.32  tff(c_7085, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k5_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_142, c_6968])).
% 9.03/3.32  tff(c_7114, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7085])).
% 9.03/3.32  tff(c_589, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, A_77)=k5_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_413])).
% 9.03/3.32  tff(c_604, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_77, k1_xboole_0))=k5_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_589, c_247])).
% 9.03/3.32  tff(c_224, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k5_xboole_0(B_66, k5_xboole_0(A_65, B_66)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_10])).
% 9.03/3.32  tff(c_497, plain, (![C_76]: (k5_xboole_0(C_76, k5_xboole_0(k1_xboole_0, C_76))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_413, c_224])).
% 9.03/3.32  tff(c_921, plain, (![C_89]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, C_89))=k5_xboole_0(C_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_497, c_247])).
% 9.03/3.32  tff(c_985, plain, (![A_77]: (k5_xboole_0(k5_xboole_0(A_77, k1_xboole_0), k1_xboole_0)=k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, A_77)))), inference(superposition, [status(thm), theory('equality')], [c_604, c_921])).
% 9.03/3.32  tff(c_1058, plain, (![A_77]: (k5_xboole_0(k5_xboole_0(A_77, k1_xboole_0), k1_xboole_0)=k5_xboole_0(k1_xboole_0, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_985])).
% 9.03/3.32  tff(c_7122, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, A_77)=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_7114, c_7114, c_1058])).
% 9.03/3.32  tff(c_7710, plain, (![A_191, C_192]: (k5_xboole_0(A_191, k5_xboole_0(A_191, C_192))=C_192)), inference(demodulation, [status(thm), theory('equality')], [c_7122, c_247])).
% 9.03/3.32  tff(c_8939, plain, (![B_203, A_204]: (k5_xboole_0(B_203, k4_xboole_0(A_204, B_203))=k2_xboole_0(A_204, B_203))), inference(superposition, [status(thm), theory('equality')], [c_6201, c_7710])).
% 9.03/3.32  tff(c_9047, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), k1_xboole_0)=k2_xboole_0(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_8939])).
% 9.03/3.32  tff(c_10275, plain, (![A_222, B_223]: (k2_xboole_0(A_222, k2_xboole_0(B_223, A_222))=k2_xboole_0(B_223, A_222))), inference(demodulation, [status(thm), theory('equality')], [c_7114, c_9047])).
% 9.03/3.32  tff(c_6062, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k4_xboole_0(B_14, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_479])).
% 9.03/3.32  tff(c_10316, plain, (![A_222, B_223]: (k5_xboole_0(A_222, k2_xboole_0(B_223, A_222))=k4_xboole_0(k2_xboole_0(B_223, A_222), A_222))), inference(superposition, [status(thm), theory('equality')], [c_10275, c_6062])).
% 9.03/3.32  tff(c_10403, plain, (![B_223, A_222]: (k4_xboole_0(k2_xboole_0(B_223, A_222), A_222)=k4_xboole_0(B_223, A_222))), inference(demodulation, [status(thm), theory('equality')], [c_6201, c_10316])).
% 9.03/3.32  tff(c_30, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.03/3.32  tff(c_15268, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10403, c_30])).
% 9.03/3.32  tff(c_15412, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_15268])).
% 9.03/3.32  tff(c_15416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_15412])).
% 9.03/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/3.32  
% 9.03/3.32  Inference rules
% 9.03/3.32  ----------------------
% 9.03/3.32  #Ref     : 0
% 9.03/3.32  #Sup     : 3741
% 9.03/3.32  #Fact    : 0
% 9.03/3.32  #Define  : 0
% 9.03/3.32  #Split   : 1
% 9.03/3.32  #Chain   : 0
% 9.03/3.32  #Close   : 0
% 9.03/3.32  
% 9.03/3.32  Ordering : KBO
% 9.03/3.32  
% 9.03/3.32  Simplification rules
% 9.03/3.32  ----------------------
% 9.03/3.32  #Subsume      : 158
% 9.03/3.32  #Demod        : 4814
% 9.03/3.32  #Tautology    : 2054
% 9.03/3.32  #SimpNegUnit  : 1
% 9.03/3.32  #BackRed      : 23
% 9.03/3.32  
% 9.03/3.32  #Partial instantiations: 0
% 9.03/3.32  #Strategies tried      : 1
% 9.03/3.32  
% 9.03/3.32  Timing (in seconds)
% 9.03/3.32  ----------------------
% 9.03/3.32  Preprocessing        : 0.31
% 9.03/3.32  Parsing              : 0.17
% 9.03/3.32  CNF conversion       : 0.02
% 9.03/3.32  Main loop            : 2.24
% 9.03/3.32  Inferencing          : 0.51
% 9.03/3.32  Reduction            : 1.28
% 9.03/3.32  Demodulation         : 1.14
% 9.03/3.32  BG Simplification    : 0.07
% 9.03/3.32  Subsumption          : 0.27
% 9.03/3.32  Abstraction          : 0.12
% 9.03/3.32  MUC search           : 0.00
% 9.03/3.32  Cooper               : 0.00
% 9.03/3.32  Total                : 2.58
% 9.03/3.32  Index Insertion      : 0.00
% 9.03/3.32  Index Deletion       : 0.00
% 9.03/3.32  Index Matching       : 0.00
% 9.03/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
