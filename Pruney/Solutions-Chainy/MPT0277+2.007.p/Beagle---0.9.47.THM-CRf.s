%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 27.39s
% Output     : CNFRefutation 27.39s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 660 expanded)
%              Number of leaves         :   35 ( 205 expanded)
%              Depth                    :    8
%              Number of atoms          :  281 (1493 expanded)
%              Number of equality atoms :  244 (1397 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_54] : k3_tarski(k1_tarski(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_237,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_246,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_237])).

tff(c_249,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_246])).

tff(c_118,plain,(
    ! [B_61,A_62] : k5_xboole_0(B_61,A_62) = k5_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [B_61] : k5_xboole_0(k1_xboole_0,B_61) = B_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_76621,plain,(
    ! [A_879,B_880] : k5_xboole_0(k5_xboole_0(A_879,B_880),k2_xboole_0(A_879,B_880)) = k3_xboole_0(A_879,B_880) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76681,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_76621])).

tff(c_76689,plain,(
    ! [A_881] : k3_xboole_0(A_881,A_881) = A_881 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_138,c_76681])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76695,plain,(
    ! [A_881] : k5_xboole_0(A_881,A_881) = k4_xboole_0(A_881,A_881) ),
    inference(superposition,[status(thm),theory(equality)],[c_76689,c_4])).

tff(c_76700,plain,(
    ! [A_881] : k4_xboole_0(A_881,A_881) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_76695])).

tff(c_75162,plain,(
    ! [A_788,B_789] : k5_xboole_0(k5_xboole_0(A_788,B_789),k2_xboole_0(A_788,B_789)) = k3_xboole_0(A_788,B_789) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75253,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_75162])).

tff(c_75261,plain,(
    ! [A_790] : k3_xboole_0(A_790,A_790) = A_790 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_249,c_75253])).

tff(c_75267,plain,(
    ! [A_790] : k5_xboole_0(A_790,A_790) = k4_xboole_0(A_790,A_790) ),
    inference(superposition,[status(thm),theory(equality)],[c_75261,c_4])).

tff(c_75272,plain,(
    ! [A_790] : k4_xboole_0(A_790,A_790) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75267])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_214,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_362,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_250,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_461,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1387,plain,(
    ! [A_137,B_138] : k5_xboole_0(k5_xboole_0(A_137,B_138),k2_xboole_0(A_137,B_138)) = k3_xboole_0(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1496,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1387])).

tff(c_1507,plain,(
    ! [A_139] : k3_xboole_0(A_139,A_139) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_138,c_1496])).

tff(c_1523,plain,(
    ! [A_139] : k5_xboole_0(A_139,A_139) = k4_xboole_0(A_139,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_4])).

tff(c_1530,plain,(
    ! [A_139] : k4_xboole_0(A_139,A_139) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1523])).

tff(c_70,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2184,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2523,plain,(
    ! [B_175,C_176,A_177] :
      ( k2_tarski(B_175,C_176) = A_177
      | k1_tarski(C_176) = A_177
      | k1_tarski(B_175) = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,k2_tarski(B_175,C_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32106,plain,(
    ! [B_354,C_355,A_356] :
      ( k2_tarski(B_354,C_355) = A_356
      | k1_tarski(C_355) = A_356
      | k1_tarski(B_354) = A_356
      | k1_xboole_0 = A_356
      | k4_xboole_0(A_356,k2_tarski(B_354,C_355)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_2523])).

tff(c_32126,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2184,c_32106])).

tff(c_32155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_362,c_250,c_461,c_32126])).

tff(c_32156,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_32235,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32156])).

tff(c_68,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_565,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_32236,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32235,c_565])).

tff(c_32239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_32236])).

tff(c_32240,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32156])).

tff(c_32242,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32240])).

tff(c_46,plain,(
    ! [B_50,C_51] : r1_tarski(k1_xboole_0,k2_tarski(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_309,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k1_xboole_0
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_337,plain,(
    ! [B_50,C_51] : k4_xboole_0(k1_xboole_0,k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_309])).

tff(c_32263,plain,(
    ! [B_50,C_51] : k4_xboole_0('#skF_1',k2_tarski(B_50,C_51)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32242,c_32242,c_337])).

tff(c_32254,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32242,c_565])).

tff(c_32624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32263,c_32254])).

tff(c_32625,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32240])).

tff(c_32627,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32625])).

tff(c_42,plain,(
    ! [C_51,B_50] : r1_tarski(k1_tarski(C_51),k2_tarski(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32802,plain,(
    ! [B_381] : r1_tarski('#skF_1',k2_tarski(B_381,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32627,c_42])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32813,plain,(
    ! [B_381] : k4_xboole_0('#skF_1',k2_tarski(B_381,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32802,c_10])).

tff(c_32879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32813,c_565])).

tff(c_32880,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32625])).

tff(c_44,plain,(
    ! [B_50,C_51] : r1_tarski(k1_tarski(B_50),k2_tarski(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_335,plain,(
    ! [B_50,C_51] : k4_xboole_0(k1_tarski(B_50),k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_309])).

tff(c_32902,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32880,c_335])).

tff(c_33159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32902,c_565])).

tff(c_33160,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_35582,plain,(
    ! [B_474,C_475,A_476] :
      ( k2_tarski(B_474,C_475) = A_476
      | k1_tarski(C_475) = A_476
      | k1_tarski(B_474) = A_476
      | k1_xboole_0 = A_476
      | ~ r1_tarski(A_476,k2_tarski(B_474,C_475)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71574,plain,(
    ! [B_654,C_655,A_656] :
      ( k2_tarski(B_654,C_655) = A_656
      | k1_tarski(C_655) = A_656
      | k1_tarski(B_654) = A_656
      | k1_xboole_0 = A_656
      | k4_xboole_0(A_656,k2_tarski(B_654,C_655)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_35582])).

tff(c_71612,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_33160,c_71574])).

tff(c_71641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_362,c_250,c_461,c_71612])).

tff(c_71642,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_72789,plain,(
    ! [A_697,B_698] : k5_xboole_0(k5_xboole_0(A_697,B_698),k2_xboole_0(A_697,B_698)) = k3_xboole_0(A_697,B_698) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72907,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_72789])).

tff(c_72919,plain,(
    ! [A_699] : k3_xboole_0(A_699,A_699) = A_699 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_249,c_72907])).

tff(c_72929,plain,(
    ! [A_699] : k5_xboole_0(A_699,A_699) = k4_xboole_0(A_699,A_699) ),
    inference(superposition,[status(thm),theory(equality)],[c_72919,c_4])).

tff(c_72936,plain,(
    ! [A_699] : k4_xboole_0(A_699,A_699) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_72929])).

tff(c_71643,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72156,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71643,c_54])).

tff(c_72157,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_72156])).

tff(c_72177,plain,(
    ! [B_50,C_51] : k4_xboole_0('#skF_1',k2_tarski(B_50,C_51)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72157,c_72157,c_337])).

tff(c_71692,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71643,c_68])).

tff(c_71693,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71692])).

tff(c_72169,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72157,c_71693])).

tff(c_72371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72177,c_72169])).

tff(c_72372,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72156])).

tff(c_72716,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_72372])).

tff(c_72717,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72716,c_71693])).

tff(c_72974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72936,c_72717])).

tff(c_72975,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72372])).

tff(c_72977,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_72975])).

tff(c_72992,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72977,c_335])).

tff(c_73489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72992,c_71693])).

tff(c_73490,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72975])).

tff(c_333,plain,(
    ! [C_51,B_50] : k4_xboole_0(k1_tarski(C_51),k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_309])).

tff(c_73503,plain,(
    ! [B_50] : k4_xboole_0('#skF_1',k2_tarski(B_50,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73490,c_333])).

tff(c_73994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73503,c_71693])).

tff(c_73996,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71692])).

tff(c_74059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71642,c_73996])).

tff(c_74061,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_74659,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74061,c_62])).

tff(c_74660,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_74659])).

tff(c_74678,plain,(
    ! [B_50,C_51] : k4_xboole_0('#skF_1',k2_tarski(B_50,C_51)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74660,c_74660,c_337])).

tff(c_74060,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_74674,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74660,c_74060])).

tff(c_74947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74678,c_74674])).

tff(c_74948,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74659])).

tff(c_75576,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_74948])).

tff(c_75577,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75576,c_74060])).

tff(c_75580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75272,c_75577])).

tff(c_75581,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74948])).

tff(c_75583,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_75581])).

tff(c_75592,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75583,c_335])).

tff(c_75835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75592,c_74060])).

tff(c_75836,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_75581])).

tff(c_75868,plain,(
    ! [B_50] : k4_xboole_0('#skF_1',k2_tarski(B_50,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75836,c_333])).

tff(c_76090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75868,c_74060])).

tff(c_76092,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_76729,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76092,c_58])).

tff(c_76730,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76729])).

tff(c_76217,plain,(
    ! [A_848,B_849] :
      ( k4_xboole_0(A_848,B_849) = k1_xboole_0
      | ~ r1_tarski(A_848,B_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76261,plain,(
    ! [B_50,C_51] : k4_xboole_0(k1_xboole_0,k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_76217])).

tff(c_76742,plain,(
    ! [B_50,C_51] : k4_xboole_0('#skF_1',k2_tarski(B_50,C_51)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76730,c_76730,c_76261])).

tff(c_76091,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_76748,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76730,c_76091])).

tff(c_76998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76742,c_76748])).

tff(c_76999,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76729])).

tff(c_77719,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76999])).

tff(c_77720,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77719,c_76091])).

tff(c_77723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76700,c_77720])).

tff(c_77724,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76999])).

tff(c_77726,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_77724])).

tff(c_76259,plain,(
    ! [B_50,C_51] : k4_xboole_0(k1_tarski(B_50),k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_76217])).

tff(c_77730,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77726,c_76259])).

tff(c_78035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77730,c_76091])).

tff(c_78036,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_77724])).

tff(c_76257,plain,(
    ! [C_51,B_50] : k4_xboole_0(k1_tarski(C_51),k2_tarski(B_50,C_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_76217])).

tff(c_78046,plain,(
    ! [B_50] : k4_xboole_0('#skF_1',k2_tarski(B_50,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78036,c_76257])).

tff(c_78337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78046,c_76091])).

tff(c_78339,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_78344,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78349,plain,(
    ! [A_953] : k5_xboole_0(A_953,'#skF_4') = A_953 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_16])).

tff(c_78369,plain,(
    ! [B_2] : k5_xboole_0('#skF_4',B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_78349])).

tff(c_78462,plain,(
    ! [A_964,B_965] : k3_tarski(k2_tarski(A_964,B_965)) = k2_xboole_0(A_964,B_965) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78471,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_78462])).

tff(c_78474,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_78471])).

tff(c_78959,plain,(
    ! [A_1013,B_1014] : k5_xboole_0(k5_xboole_0(A_1013,B_1014),k2_xboole_0(A_1013,B_1014)) = k3_xboole_0(A_1013,B_1014) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79007,plain,(
    ! [A_18] : k5_xboole_0('#skF_4',k2_xboole_0(A_18,A_18)) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_78344,c_78959])).

tff(c_79029,plain,(
    ! [A_1015] : k3_xboole_0(A_1015,A_1015) = A_1015 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78369,c_78474,c_79007])).

tff(c_79039,plain,(
    ! [A_1015] : k5_xboole_0(A_1015,A_1015) = k4_xboole_0(A_1015,A_1015) ),
    inference(superposition,[status(thm),theory(equality)],[c_79029,c_4])).

tff(c_79046,plain,(
    ! [A_1015] : k4_xboole_0(A_1015,A_1015) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78344,c_79039])).

tff(c_78342,plain,(
    ! [B_50,C_51] : r1_tarski('#skF_4',k2_tarski(B_50,C_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_46])).

tff(c_78504,plain,(
    ! [A_971,B_972] :
      ( k4_xboole_0(A_971,B_972) = '#skF_4'
      | ~ r1_tarski(A_971,B_972) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_10])).

tff(c_78528,plain,(
    ! [B_50,C_51] : k4_xboole_0('#skF_4',k2_tarski(B_50,C_51)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78342,c_78504])).

tff(c_66,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_78714,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_78339,c_66])).

tff(c_78715,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_78714])).

tff(c_78338,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_78456,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78339,c_78338])).

tff(c_78716,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78715,c_78456])).

tff(c_78719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78528,c_78716])).

tff(c_78720,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_78714])).

tff(c_79225,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_78720])).

tff(c_79226,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79225,c_78456])).

tff(c_79229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79046,c_79226])).

tff(c_79230,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_78720])).

tff(c_79232,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_79230])).

tff(c_78526,plain,(
    ! [B_50,C_51] : k4_xboole_0(k1_tarski(B_50),k2_tarski(B_50,C_51)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_78504])).

tff(c_79247,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_51)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_79232,c_78526])).

tff(c_79713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79247,c_78456])).

tff(c_79714,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_79230])).

tff(c_78524,plain,(
    ! [C_51,B_50] : k4_xboole_0(k1_tarski(C_51),k2_tarski(B_50,C_51)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_78504])).

tff(c_79727,plain,(
    ! [B_50] : k4_xboole_0('#skF_1',k2_tarski(B_50,'#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_79714,c_78524])).

tff(c_80079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79727,c_78456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n023.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 15:42:50 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.39/17.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.39/17.17  
% 27.39/17.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.39/17.17  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 27.39/17.17  
% 27.39/17.17  %Foreground sorts:
% 27.39/17.17  
% 27.39/17.17  
% 27.39/17.17  %Background operators:
% 27.39/17.17  
% 27.39/17.17  
% 27.39/17.17  %Foreground operators:
% 27.39/17.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.39/17.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.39/17.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.39/17.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.39/17.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 27.39/17.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 27.39/17.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.39/17.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 27.39/17.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.39/17.17  tff('#skF_5', type, '#skF_5': $i).
% 27.39/17.17  tff('#skF_6', type, '#skF_6': $i).
% 27.39/17.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.39/17.17  tff('#skF_2', type, '#skF_2': $i).
% 27.39/17.17  tff('#skF_3', type, '#skF_3': $i).
% 27.39/17.17  tff('#skF_1', type, '#skF_1': $i).
% 27.39/17.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.39/17.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 27.39/17.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.39/17.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 27.39/17.17  tff('#skF_4', type, '#skF_4': $i).
% 27.39/17.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.39/17.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.39/17.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.39/17.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.39/17.17  
% 27.39/17.20  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 27.39/17.20  tff(f_82, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 27.39/17.20  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 27.39/17.20  tff(f_80, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 27.39/17.20  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 27.39/17.20  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 27.39/17.20  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 27.39/17.20  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 27.39/17.20  tff(f_98, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 27.39/17.20  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 27.39/17.20  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 27.39/17.20  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.39/17.20  tff(c_50, plain, (![A_54]: (k3_tarski(k1_tarski(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.39/17.20  tff(c_24, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.39/17.20  tff(c_237, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.39/17.20  tff(c_246, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_237])).
% 27.39/17.20  tff(c_249, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_246])).
% 27.39/17.20  tff(c_118, plain, (![B_61, A_62]: (k5_xboole_0(B_61, A_62)=k5_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.39/17.20  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.39/17.20  tff(c_138, plain, (![B_61]: (k5_xboole_0(k1_xboole_0, B_61)=B_61)), inference(superposition, [status(thm), theory('equality')], [c_118, c_16])).
% 27.39/17.20  tff(c_76621, plain, (![A_879, B_880]: (k5_xboole_0(k5_xboole_0(A_879, B_880), k2_xboole_0(A_879, B_880))=k3_xboole_0(A_879, B_880))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.39/17.20  tff(c_76681, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_76621])).
% 27.39/17.20  tff(c_76689, plain, (![A_881]: (k3_xboole_0(A_881, A_881)=A_881)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_138, c_76681])).
% 27.39/17.20  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.39/17.20  tff(c_76695, plain, (![A_881]: (k5_xboole_0(A_881, A_881)=k4_xboole_0(A_881, A_881))), inference(superposition, [status(thm), theory('equality')], [c_76689, c_4])).
% 27.39/17.20  tff(c_76700, plain, (![A_881]: (k4_xboole_0(A_881, A_881)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_76695])).
% 27.39/17.20  tff(c_75162, plain, (![A_788, B_789]: (k5_xboole_0(k5_xboole_0(A_788, B_789), k2_xboole_0(A_788, B_789))=k3_xboole_0(A_788, B_789))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.39/17.20  tff(c_75253, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_75162])).
% 27.39/17.20  tff(c_75261, plain, (![A_790]: (k3_xboole_0(A_790, A_790)=A_790)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_249, c_75253])).
% 27.39/17.20  tff(c_75267, plain, (![A_790]: (k5_xboole_0(A_790, A_790)=k4_xboole_0(A_790, A_790))), inference(superposition, [status(thm), theory('equality')], [c_75261, c_4])).
% 27.39/17.20  tff(c_75272, plain, (![A_790]: (k4_xboole_0(A_790, A_790)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75267])).
% 27.39/17.20  tff(c_64, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_214, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 27.39/17.20  tff(c_60, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_362, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 27.39/17.20  tff(c_56, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_250, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_56])).
% 27.39/17.20  tff(c_52, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_461, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_52])).
% 27.39/17.20  tff(c_1387, plain, (![A_137, B_138]: (k5_xboole_0(k5_xboole_0(A_137, B_138), k2_xboole_0(A_137, B_138))=k3_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.39/17.20  tff(c_1496, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1387])).
% 27.39/17.20  tff(c_1507, plain, (![A_139]: (k3_xboole_0(A_139, A_139)=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_138, c_1496])).
% 27.39/17.20  tff(c_1523, plain, (![A_139]: (k5_xboole_0(A_139, A_139)=k4_xboole_0(A_139, A_139))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_4])).
% 27.39/17.20  tff(c_1530, plain, (![A_139]: (k4_xboole_0(A_139, A_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1523])).
% 27.39/17.20  tff(c_70, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_2184, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 27.39/17.20  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.39/17.20  tff(c_2523, plain, (![B_175, C_176, A_177]: (k2_tarski(B_175, C_176)=A_177 | k1_tarski(C_176)=A_177 | k1_tarski(B_175)=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, k2_tarski(B_175, C_176)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.39/17.20  tff(c_32106, plain, (![B_354, C_355, A_356]: (k2_tarski(B_354, C_355)=A_356 | k1_tarski(C_355)=A_356 | k1_tarski(B_354)=A_356 | k1_xboole_0=A_356 | k4_xboole_0(A_356, k2_tarski(B_354, C_355))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2523])).
% 27.39/17.20  tff(c_32126, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2184, c_32106])).
% 27.39/17.20  tff(c_32155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_362, c_250, c_461, c_32126])).
% 27.39/17.20  tff(c_32156, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_70])).
% 27.39/17.20  tff(c_32235, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_32156])).
% 27.39/17.20  tff(c_68, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_565, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 27.39/17.20  tff(c_32236, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32235, c_565])).
% 27.39/17.20  tff(c_32239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1530, c_32236])).
% 27.39/17.20  tff(c_32240, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_32156])).
% 27.39/17.20  tff(c_32242, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_32240])).
% 27.39/17.20  tff(c_46, plain, (![B_50, C_51]: (r1_tarski(k1_xboole_0, k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.39/17.20  tff(c_309, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k1_xboole_0 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.39/17.20  tff(c_337, plain, (![B_50, C_51]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_309])).
% 27.39/17.20  tff(c_32263, plain, (![B_50, C_51]: (k4_xboole_0('#skF_1', k2_tarski(B_50, C_51))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32242, c_32242, c_337])).
% 27.39/17.20  tff(c_32254, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32242, c_565])).
% 27.39/17.20  tff(c_32624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32263, c_32254])).
% 27.39/17.20  tff(c_32625, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_32240])).
% 27.39/17.20  tff(c_32627, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_32625])).
% 27.39/17.20  tff(c_42, plain, (![C_51, B_50]: (r1_tarski(k1_tarski(C_51), k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.39/17.20  tff(c_32802, plain, (![B_381]: (r1_tarski('#skF_1', k2_tarski(B_381, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_32627, c_42])).
% 27.39/17.20  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.39/17.20  tff(c_32813, plain, (![B_381]: (k4_xboole_0('#skF_1', k2_tarski(B_381, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32802, c_10])).
% 27.39/17.20  tff(c_32879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32813, c_565])).
% 27.39/17.20  tff(c_32880, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_32625])).
% 27.39/17.20  tff(c_44, plain, (![B_50, C_51]: (r1_tarski(k1_tarski(B_50), k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.39/17.20  tff(c_335, plain, (![B_50, C_51]: (k4_xboole_0(k1_tarski(B_50), k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_309])).
% 27.39/17.20  tff(c_32902, plain, (![C_51]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32880, c_335])).
% 27.39/17.20  tff(c_33159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32902, c_565])).
% 27.39/17.20  tff(c_33160, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 27.39/17.20  tff(c_35582, plain, (![B_474, C_475, A_476]: (k2_tarski(B_474, C_475)=A_476 | k1_tarski(C_475)=A_476 | k1_tarski(B_474)=A_476 | k1_xboole_0=A_476 | ~r1_tarski(A_476, k2_tarski(B_474, C_475)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.39/17.20  tff(c_71574, plain, (![B_654, C_655, A_656]: (k2_tarski(B_654, C_655)=A_656 | k1_tarski(C_655)=A_656 | k1_tarski(B_654)=A_656 | k1_xboole_0=A_656 | k4_xboole_0(A_656, k2_tarski(B_654, C_655))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_35582])).
% 27.39/17.20  tff(c_71612, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_33160, c_71574])).
% 27.39/17.20  tff(c_71641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_362, c_250, c_461, c_71612])).
% 27.39/17.20  tff(c_71642, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 27.39/17.20  tff(c_72789, plain, (![A_697, B_698]: (k5_xboole_0(k5_xboole_0(A_697, B_698), k2_xboole_0(A_697, B_698))=k3_xboole_0(A_697, B_698))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.39/17.20  tff(c_72907, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_72789])).
% 27.39/17.20  tff(c_72919, plain, (![A_699]: (k3_xboole_0(A_699, A_699)=A_699)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_249, c_72907])).
% 27.39/17.20  tff(c_72929, plain, (![A_699]: (k5_xboole_0(A_699, A_699)=k4_xboole_0(A_699, A_699))), inference(superposition, [status(thm), theory('equality')], [c_72919, c_4])).
% 27.39/17.20  tff(c_72936, plain, (![A_699]: (k4_xboole_0(A_699, A_699)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_72929])).
% 27.39/17.20  tff(c_71643, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 27.39/17.20  tff(c_54, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_72156, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_71643, c_54])).
% 27.39/17.20  tff(c_72157, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_72156])).
% 27.39/17.20  tff(c_72177, plain, (![B_50, C_51]: (k4_xboole_0('#skF_1', k2_tarski(B_50, C_51))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72157, c_72157, c_337])).
% 27.39/17.20  tff(c_71692, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71643, c_68])).
% 27.39/17.20  tff(c_71693, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71692])).
% 27.39/17.20  tff(c_72169, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72157, c_71693])).
% 27.39/17.20  tff(c_72371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72177, c_72169])).
% 27.39/17.20  tff(c_72372, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_72156])).
% 27.39/17.20  tff(c_72716, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_72372])).
% 27.39/17.20  tff(c_72717, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72716, c_71693])).
% 27.39/17.20  tff(c_72974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72936, c_72717])).
% 27.39/17.20  tff(c_72975, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_72372])).
% 27.39/17.20  tff(c_72977, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_72975])).
% 27.39/17.20  tff(c_72992, plain, (![C_51]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72977, c_335])).
% 27.39/17.20  tff(c_73489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72992, c_71693])).
% 27.39/17.20  tff(c_73490, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_72975])).
% 27.39/17.20  tff(c_333, plain, (![C_51, B_50]: (k4_xboole_0(k1_tarski(C_51), k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_309])).
% 27.39/17.20  tff(c_73503, plain, (![B_50]: (k4_xboole_0('#skF_1', k2_tarski(B_50, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73490, c_333])).
% 27.39/17.20  tff(c_73994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73503, c_71693])).
% 27.39/17.20  tff(c_73996, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_71692])).
% 27.39/17.20  tff(c_74059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71642, c_73996])).
% 27.39/17.20  tff(c_74061, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 27.39/17.20  tff(c_62, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_74659, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74061, c_62])).
% 27.39/17.20  tff(c_74660, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_74659])).
% 27.39/17.20  tff(c_74678, plain, (![B_50, C_51]: (k4_xboole_0('#skF_1', k2_tarski(B_50, C_51))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74660, c_74660, c_337])).
% 27.39/17.20  tff(c_74060, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 27.39/17.20  tff(c_74674, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74660, c_74060])).
% 27.39/17.20  tff(c_74947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74678, c_74674])).
% 27.39/17.20  tff(c_74948, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_74659])).
% 27.39/17.20  tff(c_75576, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_74948])).
% 27.39/17.20  tff(c_75577, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75576, c_74060])).
% 27.39/17.20  tff(c_75580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75272, c_75577])).
% 27.39/17.20  tff(c_75581, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_74948])).
% 27.39/17.20  tff(c_75583, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_75581])).
% 27.39/17.20  tff(c_75592, plain, (![C_51]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75583, c_335])).
% 27.39/17.20  tff(c_75835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75592, c_74060])).
% 27.39/17.20  tff(c_75836, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_75581])).
% 27.39/17.20  tff(c_75868, plain, (![B_50]: (k4_xboole_0('#skF_1', k2_tarski(B_50, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75836, c_333])).
% 27.39/17.20  tff(c_76090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75868, c_74060])).
% 27.39/17.20  tff(c_76092, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 27.39/17.20  tff(c_58, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_76729, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76092, c_58])).
% 27.39/17.20  tff(c_76730, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_76729])).
% 27.39/17.20  tff(c_76217, plain, (![A_848, B_849]: (k4_xboole_0(A_848, B_849)=k1_xboole_0 | ~r1_tarski(A_848, B_849))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.39/17.20  tff(c_76261, plain, (![B_50, C_51]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_76217])).
% 27.39/17.20  tff(c_76742, plain, (![B_50, C_51]: (k4_xboole_0('#skF_1', k2_tarski(B_50, C_51))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76730, c_76730, c_76261])).
% 27.39/17.20  tff(c_76091, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 27.39/17.20  tff(c_76748, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76730, c_76091])).
% 27.39/17.20  tff(c_76998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76742, c_76748])).
% 27.39/17.20  tff(c_76999, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_76729])).
% 27.39/17.20  tff(c_77719, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_76999])).
% 27.39/17.20  tff(c_77720, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77719, c_76091])).
% 27.39/17.20  tff(c_77723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76700, c_77720])).
% 27.39/17.20  tff(c_77724, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_76999])).
% 27.39/17.20  tff(c_77726, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_77724])).
% 27.39/17.20  tff(c_76259, plain, (![B_50, C_51]: (k4_xboole_0(k1_tarski(B_50), k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_76217])).
% 27.39/17.20  tff(c_77730, plain, (![C_51]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77726, c_76259])).
% 27.39/17.20  tff(c_78035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77730, c_76091])).
% 27.39/17.20  tff(c_78036, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_77724])).
% 27.39/17.20  tff(c_76257, plain, (![C_51, B_50]: (k4_xboole_0(k1_tarski(C_51), k2_tarski(B_50, C_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_76217])).
% 27.39/17.20  tff(c_78046, plain, (![B_50]: (k4_xboole_0('#skF_1', k2_tarski(B_50, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78036, c_76257])).
% 27.39/17.20  tff(c_78337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78046, c_76091])).
% 27.39/17.20  tff(c_78339, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 27.39/17.20  tff(c_78344, plain, (![A_18]: (k5_xboole_0(A_18, A_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_20])).
% 27.39/17.20  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.39/17.20  tff(c_78349, plain, (![A_953]: (k5_xboole_0(A_953, '#skF_4')=A_953)), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_16])).
% 27.39/17.20  tff(c_78369, plain, (![B_2]: (k5_xboole_0('#skF_4', B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_78349])).
% 27.39/17.20  tff(c_78462, plain, (![A_964, B_965]: (k3_tarski(k2_tarski(A_964, B_965))=k2_xboole_0(A_964, B_965))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.39/17.20  tff(c_78471, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_78462])).
% 27.39/17.20  tff(c_78474, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_78471])).
% 27.39/17.20  tff(c_78959, plain, (![A_1013, B_1014]: (k5_xboole_0(k5_xboole_0(A_1013, B_1014), k2_xboole_0(A_1013, B_1014))=k3_xboole_0(A_1013, B_1014))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.39/17.20  tff(c_79007, plain, (![A_18]: (k5_xboole_0('#skF_4', k2_xboole_0(A_18, A_18))=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_78344, c_78959])).
% 27.39/17.20  tff(c_79029, plain, (![A_1015]: (k3_xboole_0(A_1015, A_1015)=A_1015)), inference(demodulation, [status(thm), theory('equality')], [c_78369, c_78474, c_79007])).
% 27.39/17.20  tff(c_79039, plain, (![A_1015]: (k5_xboole_0(A_1015, A_1015)=k4_xboole_0(A_1015, A_1015))), inference(superposition, [status(thm), theory('equality')], [c_79029, c_4])).
% 27.39/17.20  tff(c_79046, plain, (![A_1015]: (k4_xboole_0(A_1015, A_1015)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78344, c_79039])).
% 27.39/17.20  tff(c_78342, plain, (![B_50, C_51]: (r1_tarski('#skF_4', k2_tarski(B_50, C_51)))), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_46])).
% 27.39/17.20  tff(c_78504, plain, (![A_971, B_972]: (k4_xboole_0(A_971, B_972)='#skF_4' | ~r1_tarski(A_971, B_972))), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_10])).
% 27.39/17.20  tff(c_78528, plain, (![B_50, C_51]: (k4_xboole_0('#skF_4', k2_tarski(B_50, C_51))='#skF_4')), inference(resolution, [status(thm)], [c_78342, c_78504])).
% 27.39/17.20  tff(c_66, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.39/17.20  tff(c_78714, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_78339, c_66])).
% 27.39/17.20  tff(c_78715, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_78714])).
% 27.39/17.20  tff(c_78338, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 27.39/17.20  tff(c_78456, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78339, c_78338])).
% 27.39/17.20  tff(c_78716, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78715, c_78456])).
% 27.39/17.20  tff(c_78719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78528, c_78716])).
% 27.39/17.20  tff(c_78720, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_78714])).
% 27.39/17.20  tff(c_79225, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_78720])).
% 27.39/17.20  tff(c_79226, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_79225, c_78456])).
% 27.39/17.20  tff(c_79229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79046, c_79226])).
% 27.39/17.20  tff(c_79230, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_78720])).
% 27.39/17.20  tff(c_79232, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_79230])).
% 27.39/17.20  tff(c_78526, plain, (![B_50, C_51]: (k4_xboole_0(k1_tarski(B_50), k2_tarski(B_50, C_51))='#skF_4')), inference(resolution, [status(thm)], [c_44, c_78504])).
% 27.39/17.20  tff(c_79247, plain, (![C_51]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_51))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79232, c_78526])).
% 27.39/17.20  tff(c_79713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79247, c_78456])).
% 27.39/17.20  tff(c_79714, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_79230])).
% 27.39/17.20  tff(c_78524, plain, (![C_51, B_50]: (k4_xboole_0(k1_tarski(C_51), k2_tarski(B_50, C_51))='#skF_4')), inference(resolution, [status(thm)], [c_42, c_78504])).
% 27.39/17.20  tff(c_79727, plain, (![B_50]: (k4_xboole_0('#skF_1', k2_tarski(B_50, '#skF_3'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79714, c_78524])).
% 27.39/17.20  tff(c_80079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79727, c_78456])).
% 27.39/17.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.39/17.20  
% 27.39/17.20  Inference rules
% 27.39/17.20  ----------------------
% 27.39/17.20  #Ref     : 0
% 27.39/17.20  #Sup     : 20988
% 27.39/17.20  #Fact    : 0
% 27.39/17.20  #Define  : 0
% 27.39/17.20  #Split   : 28
% 27.39/17.20  #Chain   : 0
% 27.39/17.20  #Close   : 0
% 27.39/17.20  
% 27.39/17.20  Ordering : KBO
% 27.39/17.20  
% 27.39/17.20  Simplification rules
% 27.39/17.20  ----------------------
% 27.39/17.20  #Subsume      : 1102
% 27.39/17.20  #Demod        : 27717
% 27.39/17.20  #Tautology    : 8566
% 27.39/17.20  #SimpNegUnit  : 17
% 27.39/17.20  #BackRed      : 143
% 27.39/17.20  
% 27.39/17.20  #Partial instantiations: 0
% 27.39/17.20  #Strategies tried      : 1
% 27.39/17.20  
% 27.39/17.20  Timing (in seconds)
% 27.39/17.20  ----------------------
% 27.39/17.20  Preprocessing        : 0.35
% 27.39/17.20  Parsing              : 0.18
% 27.39/17.20  CNF conversion       : 0.03
% 27.39/17.20  Main loop            : 16.15
% 27.39/17.20  Inferencing          : 1.93
% 27.39/17.20  Reduction            : 11.73
% 27.39/17.20  Demodulation         : 11.11
% 27.39/17.20  BG Simplification    : 0.32
% 27.39/17.20  Subsumption          : 1.77
% 27.39/17.20  Abstraction          : 0.52
% 27.39/17.20  MUC search           : 0.00
% 27.39/17.21  Cooper               : 0.00
% 27.39/17.21  Total                : 16.56
% 27.39/17.21  Index Insertion      : 0.00
% 27.39/17.21  Index Deletion       : 0.00
% 27.39/17.21  Index Matching       : 0.00
% 27.39/17.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
