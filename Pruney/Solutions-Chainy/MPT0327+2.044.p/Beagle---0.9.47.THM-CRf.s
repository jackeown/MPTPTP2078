%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 375 expanded)
%              Number of leaves         :   32 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 486 expanded)
%              Number of equality atoms :   55 ( 318 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_147])).

tff(c_133,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_137,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_238,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_238])).

tff(c_256,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_247])).

tff(c_424,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_482,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k5_xboole_0(B_87,k5_xboole_0(A_86,B_87))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_424])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_250,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_28,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_468,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k5_xboole_0(B_20,k3_xboole_0(A_19,B_20))) = k2_xboole_0(A_19,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_1024,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k4_xboole_0(B_114,A_113)) = k2_xboole_0(A_113,B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_468])).

tff(c_1064,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_1024])).

tff(c_1071,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1064])).

tff(c_335,plain,(
    ! [A_83,B_84] : k5_xboole_0(k5_xboole_0(A_83,B_84),k3_xboole_0(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_359,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_335])).

tff(c_374,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_359])).

tff(c_1073,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_374])).

tff(c_478,plain,(
    ! [B_4,C_88] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_424])).

tff(c_1438,plain,(
    ! [B_130,C_131] : k5_xboole_0(B_130,k5_xboole_0(B_130,C_131)) = C_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_478])).

tff(c_1478,plain,(
    ! [B_87,A_86] : k5_xboole_0(B_87,k5_xboole_0(A_86,B_87)) = k5_xboole_0(A_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_1438])).

tff(c_1525,plain,(
    ! [B_87,A_86] : k5_xboole_0(B_87,k5_xboole_0(A_86,B_87)) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1478])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tarski(A_65),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1701,plain,(
    ! [A_136,B_137] :
      ( k3_xboole_0(k1_tarski(A_136),B_137) = k1_tarski(A_136)
      | ~ r2_hidden(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_202,c_16])).

tff(c_1711,plain,(
    ! [A_136,B_137] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_136),B_137),k1_tarski(A_136)) = k2_xboole_0(k1_tarski(A_136),B_137)
      | ~ r2_hidden(A_136,B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_28])).

tff(c_1748,plain,(
    ! [A_136,B_137] :
      ( k2_xboole_0(k1_tarski(A_136),B_137) = B_137
      | ~ r2_hidden(A_136,B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_26,c_1711])).

tff(c_503,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_468])).

tff(c_1534,plain,(
    ! [B_132,A_133] : k5_xboole_0(B_132,k5_xboole_0(A_133,B_132)) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1478])).

tff(c_1437,plain,(
    ! [B_4,C_88] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_88)) = C_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_478])).

tff(c_1543,plain,(
    ! [B_132,A_133] : k5_xboole_0(B_132,A_133) = k5_xboole_0(A_133,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_1437])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = A_59
      | ~ r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(resolution,[status(thm)],[c_20,c_163])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2055,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k4_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1438])).

tff(c_2105,plain,(
    ! [A_12,B_13] : k5_xboole_0(k4_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = k3_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2055])).

tff(c_2127,plain,(
    ! [B_13,A_12] : k3_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2,c_2105])).

tff(c_3057,plain,(
    ! [B_172,A_173] : k5_xboole_0(k5_xboole_0(B_172,A_173),k3_xboole_0(A_173,B_172)) = k2_xboole_0(B_172,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_335])).

tff(c_3124,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_12,B_13),B_13),k1_xboole_0) = k2_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_2127,c_3057])).

tff(c_3215,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),B_13) = k2_xboole_0(B_13,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_18,c_1543,c_3124])).

tff(c_46,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3908,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3215,c_46])).

tff(c_3978,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_3908])).

tff(c_3982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.31  
% 5.08/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.08/2.32  
% 5.08/2.32  %Foreground sorts:
% 5.08/2.32  
% 5.08/2.32  
% 5.08/2.32  %Background operators:
% 5.08/2.32  
% 5.08/2.32  
% 5.08/2.32  %Foreground operators:
% 5.08/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.08/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.08/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.08/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.08/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.08/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.08/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.08/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.08/2.32  tff('#skF_2', type, '#skF_2': $i).
% 5.08/2.32  tff('#skF_1', type, '#skF_1': $i).
% 5.08/2.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.08/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/2.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.08/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.08/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.08/2.32  
% 5.08/2.33  tff(f_76, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 5.08/2.33  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.08/2.33  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.08/2.33  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.08/2.33  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.08/2.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.08/2.33  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.08/2.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.08/2.33  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.08/2.33  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.08/2.33  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.08/2.33  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.08/2.33  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.08/2.33  tff(c_18, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/2.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.08/2.33  tff(c_147, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/2.33  tff(c_151, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_147])).
% 5.08/2.33  tff(c_133, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.08/2.33  tff(c_137, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_133])).
% 5.08/2.33  tff(c_238, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/2.33  tff(c_247, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_137, c_238])).
% 5.08/2.33  tff(c_256, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_247])).
% 5.08/2.33  tff(c_424, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/2.33  tff(c_482, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k5_xboole_0(B_87, k5_xboole_0(A_86, B_87)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_424])).
% 5.08/2.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.08/2.33  tff(c_250, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 5.08/2.33  tff(c_28, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.08/2.33  tff(c_468, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k5_xboole_0(B_20, k3_xboole_0(A_19, B_20)))=k2_xboole_0(A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 5.08/2.33  tff(c_1024, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k4_xboole_0(B_114, A_113))=k2_xboole_0(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_468])).
% 5.08/2.33  tff(c_1064, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_151, c_1024])).
% 5.08/2.33  tff(c_1071, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1064])).
% 5.08/2.33  tff(c_335, plain, (![A_83, B_84]: (k5_xboole_0(k5_xboole_0(A_83, B_84), k3_xboole_0(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.08/2.33  tff(c_359, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_137, c_335])).
% 5.08/2.33  tff(c_374, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_359])).
% 5.08/2.33  tff(c_1073, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_374])).
% 5.08/2.33  tff(c_478, plain, (![B_4, C_88]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_256, c_424])).
% 5.08/2.33  tff(c_1438, plain, (![B_130, C_131]: (k5_xboole_0(B_130, k5_xboole_0(B_130, C_131))=C_131)), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_478])).
% 5.08/2.33  tff(c_1478, plain, (![B_87, A_86]: (k5_xboole_0(B_87, k5_xboole_0(A_86, B_87))=k5_xboole_0(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_482, c_1438])).
% 5.08/2.33  tff(c_1525, plain, (![B_87, A_86]: (k5_xboole_0(B_87, k5_xboole_0(A_86, B_87))=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1478])).
% 5.08/2.33  tff(c_26, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/2.33  tff(c_202, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.08/2.33  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.08/2.33  tff(c_1701, plain, (![A_136, B_137]: (k3_xboole_0(k1_tarski(A_136), B_137)=k1_tarski(A_136) | ~r2_hidden(A_136, B_137))), inference(resolution, [status(thm)], [c_202, c_16])).
% 5.08/2.33  tff(c_1711, plain, (![A_136, B_137]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_136), B_137), k1_tarski(A_136))=k2_xboole_0(k1_tarski(A_136), B_137) | ~r2_hidden(A_136, B_137))), inference(superposition, [status(thm), theory('equality')], [c_1701, c_28])).
% 5.08/2.33  tff(c_1748, plain, (![A_136, B_137]: (k2_xboole_0(k1_tarski(A_136), B_137)=B_137 | ~r2_hidden(A_136, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_26, c_1711])).
% 5.08/2.33  tff(c_503, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_468])).
% 5.08/2.33  tff(c_1534, plain, (![B_132, A_133]: (k5_xboole_0(B_132, k5_xboole_0(A_133, B_132))=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1478])).
% 5.08/2.33  tff(c_1437, plain, (![B_4, C_88]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_88))=C_88)), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_478])).
% 5.08/2.33  tff(c_1543, plain, (![B_132, A_133]: (k5_xboole_0(B_132, A_133)=k5_xboole_0(A_133, B_132))), inference(superposition, [status(thm), theory('equality')], [c_1534, c_1437])).
% 5.08/2.33  tff(c_20, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.08/2.33  tff(c_163, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=A_59 | ~r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.08/2.33  tff(c_175, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_163])).
% 5.08/2.33  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/2.33  tff(c_2055, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k4_xboole_0(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1438])).
% 5.08/2.33  tff(c_2105, plain, (![A_12, B_13]: (k5_xboole_0(k4_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=k3_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(superposition, [status(thm), theory('equality')], [c_175, c_2055])).
% 5.08/2.33  tff(c_2127, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k4_xboole_0(A_12, B_13))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2, c_2105])).
% 5.08/2.33  tff(c_3057, plain, (![B_172, A_173]: (k5_xboole_0(k5_xboole_0(B_172, A_173), k3_xboole_0(A_173, B_172))=k2_xboole_0(B_172, A_173))), inference(superposition, [status(thm), theory('equality')], [c_2, c_335])).
% 5.08/2.33  tff(c_3124, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_12, B_13), B_13), k1_xboole_0)=k2_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(superposition, [status(thm), theory('equality')], [c_2127, c_3057])).
% 5.08/2.33  tff(c_3215, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), B_13)=k2_xboole_0(B_13, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_18, c_1543, c_3124])).
% 5.08/2.33  tff(c_46, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.08/2.33  tff(c_3908, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3215, c_46])).
% 5.08/2.33  tff(c_3978, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1748, c_3908])).
% 5.08/2.33  tff(c_3982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3978])).
% 5.08/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/2.33  
% 5.08/2.33  Inference rules
% 5.08/2.33  ----------------------
% 5.08/2.33  #Ref     : 0
% 5.08/2.33  #Sup     : 948
% 5.08/2.33  #Fact    : 0
% 5.08/2.33  #Define  : 0
% 5.08/2.33  #Split   : 1
% 5.08/2.33  #Chain   : 0
% 5.08/2.33  #Close   : 0
% 5.08/2.33  
% 5.08/2.33  Ordering : KBO
% 5.08/2.33  
% 5.08/2.33  Simplification rules
% 5.08/2.33  ----------------------
% 5.08/2.33  #Subsume      : 38
% 5.08/2.33  #Demod        : 843
% 5.08/2.33  #Tautology    : 660
% 5.08/2.33  #SimpNegUnit  : 0
% 5.08/2.33  #BackRed      : 8
% 5.08/2.33  
% 5.08/2.33  #Partial instantiations: 0
% 5.08/2.33  #Strategies tried      : 1
% 5.08/2.33  
% 5.08/2.33  Timing (in seconds)
% 5.08/2.33  ----------------------
% 5.08/2.33  Preprocessing        : 0.48
% 5.08/2.33  Parsing              : 0.25
% 5.08/2.33  CNF conversion       : 0.03
% 5.08/2.33  Main loop            : 0.98
% 5.08/2.33  Inferencing          : 0.33
% 5.08/2.33  Reduction            : 0.40
% 5.08/2.33  Demodulation         : 0.33
% 5.08/2.33  BG Simplification    : 0.04
% 5.08/2.34  Subsumption          : 0.14
% 5.08/2.34  Abstraction          : 0.06
% 5.08/2.34  MUC search           : 0.00
% 5.08/2.34  Cooper               : 0.00
% 5.08/2.34  Total                : 1.50
% 5.08/2.34  Index Insertion      : 0.00
% 5.08/2.34  Index Deletion       : 0.00
% 5.08/2.34  Index Matching       : 0.00
% 5.08/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
