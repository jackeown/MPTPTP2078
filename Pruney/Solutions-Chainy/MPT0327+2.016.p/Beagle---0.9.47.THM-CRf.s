%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 144 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :   83 ( 167 expanded)
%              Number of equality atoms :   49 (  99 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_80,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_313,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1601,plain,(
    ! [A_161,B_162] :
      ( k2_xboole_0(k1_tarski(A_161),B_162) = B_162
      | ~ r2_hidden(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_313,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1634,plain,(
    ! [B_162,A_161] :
      ( k2_xboole_0(B_162,k1_tarski(A_161)) = B_162
      | ~ r2_hidden(A_161,B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_2])).

tff(c_48,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_237,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(A_69,B_70) = B_70
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_249,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(resolution,[status(thm)],[c_48,c_237])).

tff(c_50,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_250,plain,(
    ! [B_17] : k2_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_34,c_237])).

tff(c_121,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_143,plain,(
    ! [A_65] : k2_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_377,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_402,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_34,c_377])).

tff(c_678,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_693,plain,(
    ! [B_17] : k5_xboole_0(B_17,B_17) = k4_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_678])).

tff(c_401,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = A_29 ),
    inference(resolution,[status(thm)],[c_48,c_377])).

tff(c_690,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k5_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_678])).

tff(c_1946,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_690])).

tff(c_2973,plain,(
    ! [A_200,B_201,C_202] : k2_xboole_0(k4_xboole_0(A_200,k2_xboole_0(B_201,C_202)),k4_xboole_0(B_201,k2_xboole_0(A_200,C_202))) = k4_xboole_0(k5_xboole_0(A_200,B_201),C_202) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3016,plain,(
    ! [B_201,C_202] : k4_xboole_0(k5_xboole_0(B_201,B_201),C_202) = k4_xboole_0(B_201,k2_xboole_0(B_201,C_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2973,c_250])).

tff(c_3193,plain,(
    ! [B_203,C_204] : k4_xboole_0(k4_xboole_0(B_203,B_203),C_204) = k4_xboole_0(B_203,B_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1946,c_693,c_3016])).

tff(c_74,plain,(
    ! [C_54,B_53] : ~ r2_hidden(C_54,k4_xboole_0(B_53,k1_tarski(C_54))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3341,plain,(
    ! [C_206,B_207] : ~ r2_hidden(C_206,k4_xboole_0(B_207,B_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3193,c_74])).

tff(c_3377,plain,(
    ! [B_208,B_209] : r1_tarski(k4_xboole_0(B_208,B_208),B_209) ),
    inference(resolution,[status(thm)],[c_8,c_3341])).

tff(c_174,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_190,plain,(
    ! [A_66] : r1_tarski(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_48])).

tff(c_820,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(B_119,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_839,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_190,c_820])).

tff(c_3407,plain,(
    ! [B_208] : k4_xboole_0(B_208,B_208) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3377,c_839])).

tff(c_1947,plain,(
    ! [A_171,B_172] : k4_xboole_0(A_171,k2_xboole_0(A_171,B_172)) = k4_xboole_0(A_171,A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_690])).

tff(c_2051,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1947])).

tff(c_3780,plain,(
    ! [B_221,A_222] : k4_xboole_0(B_221,k2_xboole_0(A_222,B_221)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3407,c_2051])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)),k4_xboole_0(B_34,k2_xboole_0(A_33,C_35))) = k4_xboole_0(k5_xboole_0(A_33,B_34),C_35) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3788,plain,(
    ! [A_222,B_221] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_222,k2_xboole_0(B_221,B_221))) = k4_xboole_0(k5_xboole_0(B_221,A_222),B_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_3780,c_52])).

tff(c_7058,plain,(
    ! [B_292,A_293] : k4_xboole_0(k5_xboole_0(B_292,A_293),B_292) = k4_xboole_0(A_293,B_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_143,c_3788])).

tff(c_7136,plain,(
    ! [B_292,A_293] : k5_xboole_0(B_292,k4_xboole_0(A_293,B_292)) = k2_xboole_0(B_292,k5_xboole_0(B_292,A_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7058,c_50])).

tff(c_7398,plain,(
    ! [B_302,A_303] : k2_xboole_0(B_302,k5_xboole_0(B_302,A_303)) = k2_xboole_0(B_302,A_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7136])).

tff(c_7513,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_7398])).

tff(c_7544,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_7513])).

tff(c_78,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_82,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_78])).

tff(c_11362,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7544,c_82])).

tff(c_11363,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11362])).

tff(c_11614,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1634,c_11363])).

tff(c_11618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.62  
% 7.16/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.63  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.16/2.63  
% 7.16/2.63  %Foreground sorts:
% 7.16/2.63  
% 7.16/2.63  
% 7.16/2.63  %Background operators:
% 7.16/2.63  
% 7.16/2.63  
% 7.16/2.63  %Foreground operators:
% 7.16/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.16/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.16/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.16/2.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.16/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.16/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.16/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.16/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.16/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.16/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.16/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.16/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.16/2.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.16/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.16/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.16/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.16/2.63  
% 7.16/2.64  tff(f_105, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 7.16/2.64  tff(f_86, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.16/2.64  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.16/2.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.16/2.64  tff(f_70, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.16/2.64  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.16/2.64  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.16/2.64  tff(f_60, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.16/2.64  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.16/2.64  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.16/2.64  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.16/2.64  tff(f_74, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 7.16/2.64  tff(f_100, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.16/2.64  tff(c_80, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.16/2.64  tff(c_313, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.64  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.16/2.64  tff(c_1601, plain, (![A_161, B_162]: (k2_xboole_0(k1_tarski(A_161), B_162)=B_162 | ~r2_hidden(A_161, B_162))), inference(resolution, [status(thm)], [c_313, c_38])).
% 7.16/2.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.16/2.64  tff(c_1634, plain, (![B_162, A_161]: (k2_xboole_0(B_162, k1_tarski(A_161))=B_162 | ~r2_hidden(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_2])).
% 7.16/2.64  tff(c_48, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.16/2.64  tff(c_237, plain, (![A_69, B_70]: (k2_xboole_0(A_69, B_70)=B_70 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.16/2.64  tff(c_249, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(resolution, [status(thm)], [c_48, c_237])).
% 7.16/2.64  tff(c_50, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.16/2.64  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.16/2.64  tff(c_250, plain, (![B_17]: (k2_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_34, c_237])).
% 7.16/2.64  tff(c_121, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.16/2.64  tff(c_40, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.16/2.64  tff(c_143, plain, (![A_65]: (k2_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_121, c_40])).
% 7.16/2.64  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.16/2.64  tff(c_377, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.16/2.64  tff(c_402, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_34, c_377])).
% 7.16/2.64  tff(c_678, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.16/2.64  tff(c_693, plain, (![B_17]: (k5_xboole_0(B_17, B_17)=k4_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_402, c_678])).
% 7.16/2.64  tff(c_401, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k2_xboole_0(A_29, B_30))=A_29)), inference(resolution, [status(thm)], [c_48, c_377])).
% 7.16/2.64  tff(c_690, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k5_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_401, c_678])).
% 7.16/2.64  tff(c_1946, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k4_xboole_0(A_29, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_690])).
% 7.16/2.64  tff(c_2973, plain, (![A_200, B_201, C_202]: (k2_xboole_0(k4_xboole_0(A_200, k2_xboole_0(B_201, C_202)), k4_xboole_0(B_201, k2_xboole_0(A_200, C_202)))=k4_xboole_0(k5_xboole_0(A_200, B_201), C_202))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.16/2.64  tff(c_3016, plain, (![B_201, C_202]: (k4_xboole_0(k5_xboole_0(B_201, B_201), C_202)=k4_xboole_0(B_201, k2_xboole_0(B_201, C_202)))), inference(superposition, [status(thm), theory('equality')], [c_2973, c_250])).
% 7.16/2.64  tff(c_3193, plain, (![B_203, C_204]: (k4_xboole_0(k4_xboole_0(B_203, B_203), C_204)=k4_xboole_0(B_203, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_1946, c_693, c_3016])).
% 7.16/2.64  tff(c_74, plain, (![C_54, B_53]: (~r2_hidden(C_54, k4_xboole_0(B_53, k1_tarski(C_54))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.16/2.64  tff(c_3341, plain, (![C_206, B_207]: (~r2_hidden(C_206, k4_xboole_0(B_207, B_207)))), inference(superposition, [status(thm), theory('equality')], [c_3193, c_74])).
% 7.16/2.64  tff(c_3377, plain, (![B_208, B_209]: (r1_tarski(k4_xboole_0(B_208, B_208), B_209))), inference(resolution, [status(thm)], [c_8, c_3341])).
% 7.16/2.64  tff(c_174, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_121, c_40])).
% 7.16/2.64  tff(c_190, plain, (![A_66]: (r1_tarski(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_174, c_48])).
% 7.16/2.64  tff(c_820, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(B_119, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.16/2.64  tff(c_839, plain, (![A_66]: (k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_190, c_820])).
% 7.16/2.64  tff(c_3407, plain, (![B_208]: (k4_xboole_0(B_208, B_208)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3377, c_839])).
% 7.16/2.64  tff(c_1947, plain, (![A_171, B_172]: (k4_xboole_0(A_171, k2_xboole_0(A_171, B_172))=k4_xboole_0(A_171, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_690])).
% 7.16/2.64  tff(c_2051, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1947])).
% 7.16/2.64  tff(c_3780, plain, (![B_221, A_222]: (k4_xboole_0(B_221, k2_xboole_0(A_222, B_221))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3407, c_2051])).
% 7.16/2.64  tff(c_52, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)), k4_xboole_0(B_34, k2_xboole_0(A_33, C_35)))=k4_xboole_0(k5_xboole_0(A_33, B_34), C_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.16/2.64  tff(c_3788, plain, (![A_222, B_221]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_222, k2_xboole_0(B_221, B_221)))=k4_xboole_0(k5_xboole_0(B_221, A_222), B_221))), inference(superposition, [status(thm), theory('equality')], [c_3780, c_52])).
% 7.16/2.64  tff(c_7058, plain, (![B_292, A_293]: (k4_xboole_0(k5_xboole_0(B_292, A_293), B_292)=k4_xboole_0(A_293, B_292))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_143, c_3788])).
% 7.16/2.64  tff(c_7136, plain, (![B_292, A_293]: (k5_xboole_0(B_292, k4_xboole_0(A_293, B_292))=k2_xboole_0(B_292, k5_xboole_0(B_292, A_293)))), inference(superposition, [status(thm), theory('equality')], [c_7058, c_50])).
% 7.16/2.64  tff(c_7398, plain, (![B_302, A_303]: (k2_xboole_0(B_302, k5_xboole_0(B_302, A_303))=k2_xboole_0(B_302, A_303))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7136])).
% 7.16/2.64  tff(c_7513, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, k2_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_7398])).
% 7.16/2.64  tff(c_7544, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_7513])).
% 7.16/2.64  tff(c_78, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.16/2.64  tff(c_82, plain, (k2_xboole_0(k1_tarski('#skF_4'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_78])).
% 7.16/2.64  tff(c_11362, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7544, c_82])).
% 7.16/2.64  tff(c_11363, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11362])).
% 7.16/2.64  tff(c_11614, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1634, c_11363])).
% 7.16/2.64  tff(c_11618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_11614])).
% 7.16/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.64  
% 7.16/2.64  Inference rules
% 7.16/2.64  ----------------------
% 7.16/2.64  #Ref     : 0
% 7.16/2.64  #Sup     : 2889
% 7.16/2.64  #Fact    : 0
% 7.16/2.64  #Define  : 0
% 7.16/2.64  #Split   : 0
% 7.16/2.64  #Chain   : 0
% 7.16/2.64  #Close   : 0
% 7.16/2.64  
% 7.16/2.64  Ordering : KBO
% 7.16/2.64  
% 7.16/2.64  Simplification rules
% 7.16/2.64  ----------------------
% 7.16/2.64  #Subsume      : 423
% 7.16/2.64  #Demod        : 2753
% 7.16/2.64  #Tautology    : 1617
% 7.16/2.64  #SimpNegUnit  : 63
% 7.16/2.64  #BackRed      : 12
% 7.16/2.64  
% 7.16/2.64  #Partial instantiations: 0
% 7.16/2.64  #Strategies tried      : 1
% 7.16/2.64  
% 7.16/2.64  Timing (in seconds)
% 7.16/2.64  ----------------------
% 7.16/2.64  Preprocessing        : 0.36
% 7.16/2.64  Parsing              : 0.19
% 7.16/2.64  CNF conversion       : 0.03
% 7.16/2.64  Main loop            : 1.47
% 7.16/2.64  Inferencing          : 0.40
% 7.16/2.64  Reduction            : 0.69
% 7.16/2.65  Demodulation         : 0.56
% 7.16/2.65  BG Simplification    : 0.05
% 7.16/2.65  Subsumption          : 0.24
% 7.16/2.65  Abstraction          : 0.07
% 7.16/2.65  MUC search           : 0.00
% 7.16/2.65  Cooper               : 0.00
% 7.16/2.65  Total                : 1.86
% 7.16/2.65  Index Insertion      : 0.00
% 7.16/2.65  Index Deletion       : 0.00
% 7.16/2.65  Index Matching       : 0.00
% 7.16/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
