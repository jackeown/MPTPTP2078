%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0102+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 43.34s
% Output     : CNFRefutation 43.45s
% Verified   : 
% Statistics : Number of formulae       :   84 (  97 expanded)
%              Number of leaves         :   51 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  61 expanded)
%              Number of equality atoms :   47 (  60 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_436,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_127,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

tff(f_438,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_434,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_344,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_270,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_414,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_554,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_348,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_689,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_698,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_312,plain,(
    ! [A_211,B_212] : k4_xboole_0(A_211,k4_xboole_0(A_211,B_212)) = k3_xboole_0(A_211,B_212) ),
    inference(cnfTransformation,[status(thm)],[f_436])).

tff(c_106,plain,(
    ! [A_46] : k3_xboole_0(A_46,A_46) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_13394,plain,(
    ! [A_815,B_816,C_817] : k4_xboole_0(k3_xboole_0(A_815,B_816),C_817) = k3_xboole_0(A_815,k4_xboole_0(B_816,C_817)) ),
    inference(cnfTransformation,[status(thm)],[f_438])).

tff(c_13646,plain,(
    ! [A_46,C_817] : k3_xboole_0(A_46,k4_xboole_0(A_46,C_817)) = k4_xboole_0(A_46,C_817) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_13394])).

tff(c_310,plain,(
    ! [A_209,B_210] : k4_xboole_0(A_209,k3_xboole_0(A_209,B_210)) = k4_xboole_0(A_209,B_210) ),
    inference(cnfTransformation,[status(thm)],[f_434])).

tff(c_250,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k3_xboole_0(A_138,B_139)) = A_138 ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_16808,plain,(
    ! [A_891,B_892] : k4_xboole_0(k2_xboole_0(A_891,B_892),k3_xboole_0(A_891,B_892)) = k5_xboole_0(A_891,B_892) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_17035,plain,(
    ! [A_138,B_139] : k4_xboole_0(A_138,k3_xboole_0(A_138,k3_xboole_0(A_138,B_139))) = k5_xboole_0(A_138,k3_xboole_0(A_138,B_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_16808])).

tff(c_56185,plain,(
    ! [A_1487,B_1488] : k5_xboole_0(A_1487,k3_xboole_0(A_1487,B_1488)) = k4_xboole_0(A_1487,B_1488) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_17035])).

tff(c_56317,plain,(
    ! [A_46,C_817] : k5_xboole_0(A_46,k4_xboole_0(A_46,C_817)) = k4_xboole_0(A_46,k4_xboole_0(A_46,C_817)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13646,c_56185])).

tff(c_56424,plain,(
    ! [A_46,C_817] : k5_xboole_0(A_46,k4_xboole_0(A_46,C_817)) = k3_xboole_0(A_46,C_817) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_56317])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8825,plain,(
    ! [A_695,B_696] : k4_xboole_0(k2_xboole_0(A_695,B_696),B_696) = k4_xboole_0(A_695,B_696) ),
    inference(cnfTransformation,[status(thm)],[f_414])).

tff(c_8977,plain,(
    ! [B_6,A_5] : k4_xboole_0(k2_xboole_0(B_6,A_5),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_8825])).

tff(c_368,plain,(
    ! [A_273,B_274] : k2_xboole_0(A_273,k2_xboole_0(A_273,B_274)) = k2_xboole_0(A_273,B_274) ),
    inference(cnfTransformation,[status(thm)],[f_554])).

tff(c_10,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,A_9) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_968,plain,(
    ! [A_407,B_408] : k2_xboole_0(A_407,k3_xboole_0(A_407,B_408)) = A_407 ),
    inference(cnfTransformation,[status(thm)],[f_344])).

tff(c_995,plain,(
    ! [B_8,A_7] : k2_xboole_0(B_8,k3_xboole_0(A_7,B_8)) = B_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_968])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26698,plain,(
    ! [A_1065,B_1066,C_1067] : k3_xboole_0(k2_xboole_0(A_1065,B_1066),k2_xboole_0(A_1065,C_1067)) = k2_xboole_0(A_1065,k3_xboole_0(B_1066,C_1067)) ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_27098,plain,(
    ! [A_44,B_1066] : k3_xboole_0(k2_xboole_0(A_44,B_1066),A_44) = k2_xboole_0(A_44,k3_xboole_0(B_1066,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_26698])).

tff(c_27137,plain,(
    ! [A_44,B_1066] : k3_xboole_0(k2_xboole_0(A_44,B_1066),A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_27098])).

tff(c_173514,plain,(
    ! [B_2223,A_2224] : k4_xboole_0(k2_xboole_0(B_2223,A_2224),k3_xboole_0(A_2224,B_2223)) = k5_xboole_0(A_2224,B_2223) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_16808])).

tff(c_174245,plain,(
    ! [A_44,B_1066] : k4_xboole_0(k2_xboole_0(A_44,k2_xboole_0(A_44,B_1066)),A_44) = k5_xboole_0(k2_xboole_0(A_44,B_1066),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_27137,c_173514])).

tff(c_174494,plain,(
    ! [A_44,B_1066] : k5_xboole_0(A_44,k2_xboole_0(A_44,B_1066)) = k4_xboole_0(B_1066,A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8977,c_368,c_10,c_174245])).

tff(c_426,plain,(
    ! [A_341,B_342,C_343] : k5_xboole_0(k5_xboole_0(A_341,B_342),C_343) = k5_xboole_0(A_341,k5_xboole_0(B_342,C_343)) ),
    inference(cnfTransformation,[status(thm)],[f_689])).

tff(c_434,plain,(
    k5_xboole_0(k5_xboole_0('#skF_21','#skF_22'),k2_xboole_0('#skF_21','#skF_22')) != k3_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_698])).

tff(c_437,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k2_xboole_0('#skF_21','#skF_22'))) != k3_xboole_0('#skF_21','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_434])).

tff(c_452,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k2_xboole_0('#skF_21','#skF_22'))) != k3_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_437])).

tff(c_453,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k2_xboole_0('#skF_22','#skF_21'))) != k3_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_452])).

tff(c_174534,plain,(
    k5_xboole_0('#skF_21',k4_xboole_0('#skF_21','#skF_22')) != k3_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174494,c_453])).

tff(c_174543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_56424,c_174534])).
%------------------------------------------------------------------------------
