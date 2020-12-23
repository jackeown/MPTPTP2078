%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0099+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 9.36s
% Output     : CNFRefutation 9.36s
% Verified   : 
% Statistics : Number of formulae       :   56 (  61 expanded)
%              Number of leaves         :   42 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  30 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

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

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_548,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_428,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_688,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_449,plain,(
    ! [A_348] :
      ( k1_xboole_0 = A_348
      | ~ v1_xboole_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_548])).

tff(c_458,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_449])).

tff(c_304,plain,(
    ! [A_203,B_204] : k4_xboole_0(A_203,k2_xboole_0(A_203,B_204)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_428])).

tff(c_1238,plain,(
    ! [A_413,B_414] : k4_xboole_0(A_413,k2_xboole_0(A_413,B_414)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_304])).

tff(c_1266,plain,(
    ! [A_134] : k4_xboole_0(A_134,A_134) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1238])).

tff(c_13939,plain,(
    ! [A_835,B_836] : k2_xboole_0(k4_xboole_0(A_835,B_836),k4_xboole_0(B_836,A_835)) = k5_xboole_0(A_835,B_836) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14079,plain,(
    ! [B_836] : k5_xboole_0(B_836,B_836) = k4_xboole_0(B_836,B_836) ),
    inference(superposition,[status(thm),theory(equality)],[c_13939,c_104])).

tff(c_14179,plain,(
    ! [B_836] : k5_xboole_0(B_836,B_836) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_14079])).

tff(c_424,plain,(
    k5_xboole_0('#skF_21','#skF_21') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_688])).

tff(c_460,plain,(
    k5_xboole_0('#skF_21','#skF_21') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_424])).

tff(c_14210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14179,c_460])).
%------------------------------------------------------------------------------
