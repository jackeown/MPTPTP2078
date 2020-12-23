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
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 180 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 203 expanded)
%              Number of equality atoms :   65 ( 138 expanded)
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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12796,plain,(
    ! [A_335,B_336] : k5_xboole_0(A_335,k3_xboole_0(A_335,B_336)) = k4_xboole_0(A_335,B_336) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12813,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12796])).

tff(c_12816,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12813])).

tff(c_52,plain,(
    ! [B_67] : k4_xboole_0(k1_tarski(B_67),k1_tarski(B_67)) != k1_tarski(B_67) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12826,plain,(
    ! [B_67] : k1_tarski(B_67) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12816,c_52])).

tff(c_12516,plain,(
    ! [A_313,B_314] : k5_xboole_0(A_313,k3_xboole_0(A_313,B_314)) = k4_xboole_0(A_313,B_314) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12533,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12516])).

tff(c_12536,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12533])).

tff(c_12537,plain,(
    ! [B_67] : k1_tarski(B_67) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12536,c_52])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1122,plain,(
    ! [A_149,B_150] : k5_xboole_0(k5_xboole_0(A_149,B_150),k2_xboole_0(A_149,B_150)) = k3_xboole_0(A_149,B_150) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6551,plain,(
    ! [A_249,B_250] : k5_xboole_0(A_249,k5_xboole_0(B_250,k2_xboole_0(A_249,B_250))) = k3_xboole_0(A_249,B_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_18])).

tff(c_134,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,A_80) = k5_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_803,plain,(
    ! [A_140,B_141,C_142] : k5_xboole_0(k5_xboole_0(A_140,B_141),C_142) = k5_xboole_0(A_140,k5_xboole_0(B_141,C_142)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_867,plain,(
    ! [A_19,C_142] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_142)) = k5_xboole_0(k1_xboole_0,C_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_803])).

tff(c_880,plain,(
    ! [A_19,C_142] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_142)) = C_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_867])).

tff(c_6604,plain,(
    ! [B_250,A_249] : k5_xboole_0(B_250,k2_xboole_0(A_249,B_250)) = k5_xboole_0(A_249,k3_xboole_0(A_249,B_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6551,c_880])).

tff(c_6721,plain,(
    ! [B_250,A_249] : k5_xboole_0(B_250,k2_xboole_0(A_249,B_250)) = k4_xboole_0(A_249,B_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6604])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(k1_tarski(A_62),B_63) = k1_tarski(A_62)
      | r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_282,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_315,plain,(
    ! [B_96,A_97] : k3_tarski(k2_tarski(B_96,A_97)) = k2_xboole_0(A_97,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_282])).

tff(c_327,plain,(
    ! [B_65,A_64] : k2_xboole_0(B_65,A_64) = k2_xboole_0(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_315])).

tff(c_6746,plain,(
    ! [B_251,A_252] : k5_xboole_0(B_251,k2_xboole_0(A_252,B_251)) = k4_xboole_0(A_252,B_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6604])).

tff(c_881,plain,(
    ! [A_143,C_144] : k5_xboole_0(A_143,k5_xboole_0(A_143,C_144)) = C_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_867])).

tff(c_924,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_881])).

tff(c_7085,plain,(
    ! [A_255,B_256] : k5_xboole_0(k2_xboole_0(A_255,B_256),k4_xboole_0(A_255,B_256)) = B_256 ),
    inference(superposition,[status(thm),theory(equality)],[c_6746,c_924])).

tff(c_8781,plain,(
    ! [A_274,B_275] : k5_xboole_0(k2_xboole_0(A_274,B_275),k4_xboole_0(B_275,A_274)) = A_274 ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_7085])).

tff(c_8897,plain,(
    ! [B_63,A_62] :
      ( k5_xboole_0(k2_xboole_0(B_63,k1_tarski(A_62)),k1_tarski(A_62)) = B_63
      | r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_8781])).

tff(c_12184,plain,(
    ! [B_300,A_301] :
      ( k4_xboole_0(B_300,k1_tarski(A_301)) = B_300
      | r2_hidden(A_301,B_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6721,c_2,c_8897])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_281,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_12272,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12184,c_281])).

tff(c_12339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_12272])).

tff(c_12340,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_44,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12341,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12350,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12341,c_64])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12354,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12350,c_12])).

tff(c_12468,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12354])).

tff(c_12472,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_12468])).

tff(c_12476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12340,c_12472])).

tff(c_12477,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12354])).

tff(c_12549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12537,c_12477])).

tff(c_12550,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12551,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12552,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_12554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_12552])).

tff(c_12555,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12706,plain,(
    ! [A_323,B_324] :
      ( k1_xboole_0 = A_323
      | ~ r1_tarski(A_323,k4_xboole_0(B_324,A_323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12709,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12555,c_12706])).

tff(c_12760,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12709])).

tff(c_12763,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_12760])).

tff(c_12767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12550,c_12763])).

tff(c_12768,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12709])).

tff(c_12839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12826,c_12768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.07/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/3.03  
% 8.07/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/3.03  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.07/3.03  
% 8.07/3.03  %Foreground sorts:
% 8.07/3.03  
% 8.07/3.03  
% 8.07/3.03  %Background operators:
% 8.07/3.03  
% 8.07/3.03  
% 8.07/3.03  %Foreground operators:
% 8.07/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.07/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.07/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.07/3.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.07/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.07/3.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.07/3.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.07/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.07/3.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.07/3.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.07/3.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.07/3.03  tff('#skF_2', type, '#skF_2': $i).
% 8.07/3.03  tff('#skF_3', type, '#skF_3': $i).
% 8.07/3.03  tff('#skF_1', type, '#skF_1': $i).
% 8.07/3.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.07/3.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.07/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.07/3.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.07/3.03  tff('#skF_4', type, '#skF_4': $i).
% 8.07/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.07/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.07/3.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.07/3.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.07/3.03  
% 8.07/3.05  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.07/3.05  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.07/3.05  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.07/3.05  tff(f_83, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 8.07/3.05  tff(f_97, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.07/3.05  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.07/3.05  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.07/3.05  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.07/3.05  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.07/3.05  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 8.07/3.05  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.07/3.05  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.07/3.05  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.07/3.05  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 8.07/3.05  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.07/3.05  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.07/3.05  tff(c_12796, plain, (![A_335, B_336]: (k5_xboole_0(A_335, k3_xboole_0(A_335, B_336))=k4_xboole_0(A_335, B_336))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.07/3.05  tff(c_12813, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12796])).
% 8.07/3.05  tff(c_12816, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12813])).
% 8.07/3.05  tff(c_52, plain, (![B_67]: (k4_xboole_0(k1_tarski(B_67), k1_tarski(B_67))!=k1_tarski(B_67))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.07/3.05  tff(c_12826, plain, (![B_67]: (k1_tarski(B_67)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12816, c_52])).
% 8.07/3.05  tff(c_12516, plain, (![A_313, B_314]: (k5_xboole_0(A_313, k3_xboole_0(A_313, B_314))=k4_xboole_0(A_313, B_314))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.07/3.05  tff(c_12533, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12516])).
% 8.07/3.05  tff(c_12536, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12533])).
% 8.07/3.05  tff(c_12537, plain, (![B_67]: (k1_tarski(B_67)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12536, c_52])).
% 8.07/3.05  tff(c_62, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.07/3.05  tff(c_120, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 8.07/3.05  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.07/3.05  tff(c_1122, plain, (![A_149, B_150]: (k5_xboole_0(k5_xboole_0(A_149, B_150), k2_xboole_0(A_149, B_150))=k3_xboole_0(A_149, B_150))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.07/3.05  tff(c_18, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.07/3.05  tff(c_6551, plain, (![A_249, B_250]: (k5_xboole_0(A_249, k5_xboole_0(B_250, k2_xboole_0(A_249, B_250)))=k3_xboole_0(A_249, B_250))), inference(superposition, [status(thm), theory('equality')], [c_1122, c_18])).
% 8.07/3.05  tff(c_134, plain, (![B_79, A_80]: (k5_xboole_0(B_79, A_80)=k5_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.07/3.05  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.07/3.05  tff(c_150, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 8.07/3.05  tff(c_803, plain, (![A_140, B_141, C_142]: (k5_xboole_0(k5_xboole_0(A_140, B_141), C_142)=k5_xboole_0(A_140, k5_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.07/3.05  tff(c_867, plain, (![A_19, C_142]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_142))=k5_xboole_0(k1_xboole_0, C_142))), inference(superposition, [status(thm), theory('equality')], [c_20, c_803])).
% 8.07/3.05  tff(c_880, plain, (![A_19, C_142]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_142))=C_142)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_867])).
% 8.07/3.05  tff(c_6604, plain, (![B_250, A_249]: (k5_xboole_0(B_250, k2_xboole_0(A_249, B_250))=k5_xboole_0(A_249, k3_xboole_0(A_249, B_250)))), inference(superposition, [status(thm), theory('equality')], [c_6551, c_880])).
% 8.07/3.05  tff(c_6721, plain, (![B_250, A_249]: (k5_xboole_0(B_250, k2_xboole_0(A_249, B_250))=k4_xboole_0(A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6604])).
% 8.07/3.05  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.07/3.05  tff(c_48, plain, (![A_62, B_63]: (k4_xboole_0(k1_tarski(A_62), B_63)=k1_tarski(A_62) | r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.07/3.05  tff(c_50, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.07/3.05  tff(c_24, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.07/3.05  tff(c_282, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.07/3.05  tff(c_315, plain, (![B_96, A_97]: (k3_tarski(k2_tarski(B_96, A_97))=k2_xboole_0(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_24, c_282])).
% 8.07/3.05  tff(c_327, plain, (![B_65, A_64]: (k2_xboole_0(B_65, A_64)=k2_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_50, c_315])).
% 8.07/3.05  tff(c_6746, plain, (![B_251, A_252]: (k5_xboole_0(B_251, k2_xboole_0(A_252, B_251))=k4_xboole_0(A_252, B_251))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6604])).
% 8.07/3.05  tff(c_881, plain, (![A_143, C_144]: (k5_xboole_0(A_143, k5_xboole_0(A_143, C_144))=C_144)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_867])).
% 8.07/3.05  tff(c_924, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_881])).
% 8.07/3.05  tff(c_7085, plain, (![A_255, B_256]: (k5_xboole_0(k2_xboole_0(A_255, B_256), k4_xboole_0(A_255, B_256))=B_256)), inference(superposition, [status(thm), theory('equality')], [c_6746, c_924])).
% 8.07/3.05  tff(c_8781, plain, (![A_274, B_275]: (k5_xboole_0(k2_xboole_0(A_274, B_275), k4_xboole_0(B_275, A_274))=A_274)), inference(superposition, [status(thm), theory('equality')], [c_327, c_7085])).
% 8.07/3.05  tff(c_8897, plain, (![B_63, A_62]: (k5_xboole_0(k2_xboole_0(B_63, k1_tarski(A_62)), k1_tarski(A_62))=B_63 | r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_48, c_8781])).
% 8.07/3.05  tff(c_12184, plain, (![B_300, A_301]: (k4_xboole_0(B_300, k1_tarski(A_301))=B_300 | r2_hidden(A_301, B_300))), inference(demodulation, [status(thm), theory('equality')], [c_6721, c_2, c_8897])).
% 8.07/3.05  tff(c_60, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.07/3.05  tff(c_281, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_60])).
% 8.07/3.05  tff(c_12272, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12184, c_281])).
% 8.07/3.05  tff(c_12339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_12272])).
% 8.07/3.05  tff(c_12340, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 8.07/3.05  tff(c_44, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.07/3.05  tff(c_12341, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 8.07/3.05  tff(c_64, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.07/3.05  tff(c_12350, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12341, c_64])).
% 8.07/3.05  tff(c_12, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.07/3.05  tff(c_12354, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12350, c_12])).
% 8.07/3.05  tff(c_12468, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_12354])).
% 8.07/3.05  tff(c_12472, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_12468])).
% 8.07/3.05  tff(c_12476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12340, c_12472])).
% 8.07/3.05  tff(c_12477, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12354])).
% 8.07/3.05  tff(c_12549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12537, c_12477])).
% 8.07/3.05  tff(c_12550, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 8.07/3.05  tff(c_12551, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 8.07/3.05  tff(c_66, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.07/3.05  tff(c_12552, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 8.07/3.05  tff(c_12554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12551, c_12552])).
% 8.07/3.05  tff(c_12555, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 8.07/3.05  tff(c_12706, plain, (![A_323, B_324]: (k1_xboole_0=A_323 | ~r1_tarski(A_323, k4_xboole_0(B_324, A_323)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.07/3.05  tff(c_12709, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12555, c_12706])).
% 8.07/3.05  tff(c_12760, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_12709])).
% 8.07/3.05  tff(c_12763, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_12760])).
% 8.07/3.05  tff(c_12767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12550, c_12763])).
% 8.07/3.05  tff(c_12768, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12709])).
% 8.07/3.05  tff(c_12839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12826, c_12768])).
% 8.07/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/3.05  
% 8.07/3.05  Inference rules
% 8.07/3.05  ----------------------
% 8.07/3.05  #Ref     : 0
% 8.07/3.05  #Sup     : 3106
% 8.07/3.05  #Fact    : 0
% 8.07/3.05  #Define  : 0
% 8.07/3.05  #Split   : 6
% 8.07/3.05  #Chain   : 0
% 8.07/3.05  #Close   : 0
% 8.07/3.05  
% 8.07/3.05  Ordering : KBO
% 8.07/3.05  
% 8.07/3.05  Simplification rules
% 8.07/3.05  ----------------------
% 8.07/3.05  #Subsume      : 280
% 8.07/3.05  #Demod        : 3431
% 8.07/3.05  #Tautology    : 1779
% 8.07/3.05  #SimpNegUnit  : 113
% 8.07/3.05  #BackRed      : 9
% 8.07/3.05  
% 8.07/3.05  #Partial instantiations: 0
% 8.07/3.05  #Strategies tried      : 1
% 8.07/3.05  
% 8.07/3.05  Timing (in seconds)
% 8.07/3.05  ----------------------
% 8.07/3.05  Preprocessing        : 0.36
% 8.07/3.05  Parsing              : 0.19
% 8.07/3.05  CNF conversion       : 0.02
% 8.07/3.05  Main loop            : 1.89
% 8.07/3.05  Inferencing          : 0.47
% 8.07/3.05  Reduction            : 0.99
% 8.07/3.05  Demodulation         : 0.86
% 8.07/3.05  BG Simplification    : 0.06
% 8.07/3.05  Subsumption          : 0.27
% 8.07/3.05  Abstraction          : 0.09
% 8.07/3.05  MUC search           : 0.00
% 8.07/3.05  Cooper               : 0.00
% 8.07/3.05  Total                : 2.29
% 8.07/3.05  Index Insertion      : 0.00
% 8.07/3.05  Index Deletion       : 0.00
% 8.07/3.05  Index Matching       : 0.00
% 8.07/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
