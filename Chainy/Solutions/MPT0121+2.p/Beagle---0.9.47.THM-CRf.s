%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0121+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:15 EST 2020

% Result     : Theorem 25.34s
% Output     : CNFRefutation 25.39s
% Verified   : 
% Statistics : Number of formulae       :   77 (  91 expanded)
%              Number of leaves         :   48 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  86 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_24 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_23 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

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

tff('#skF_19',type,(
    '#skF_19': $i )).

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

tff('#skF_23',type,(
    '#skF_23': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

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

tff(f_352,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_630,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(f_698,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_520,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_268,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_877,plain,(
    ! [B_452,A_453] :
      ( r1_xboole_0(B_452,A_453)
      | ~ r1_xboole_0(A_453,B_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_896,plain,(
    r1_xboole_0('#skF_22','#skF_21') ),
    inference(resolution,[status(thm)],[c_268,c_877])).

tff(c_270,plain,(
    r1_xboole_0('#skF_20','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_895,plain,(
    r1_xboole_0('#skF_22','#skF_20') ),
    inference(resolution,[status(thm)],[c_270,c_877])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_596,plain,(
    ! [A_419] :
      ( k1_xboole_0 = A_419
      | ~ v1_xboole_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_630])).

tff(c_605,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_596])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1497,plain,(
    ! [A_495,B_496] :
      ( k3_xboole_0(A_495,B_496) = '#skF_9'
      | ~ r1_xboole_0(A_495,B_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_80])).

tff(c_1531,plain,(
    k3_xboole_0('#skF_22','#skF_20') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_895,c_1497])).

tff(c_448,plain,(
    ! [A_343,B_344,C_345] :
      ( k3_xboole_0(A_343,k2_xboole_0(B_344,C_345)) = k3_xboole_0(A_343,C_345)
      | ~ r1_xboole_0(A_343,B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_698])).

tff(c_272,plain,(
    r1_xboole_0('#skF_19','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_897,plain,(
    r1_xboole_0('#skF_22','#skF_19') ),
    inference(resolution,[status(thm)],[c_272,c_877])).

tff(c_53009,plain,(
    ! [A_1164,B_1165,C_1166] :
      ( k3_xboole_0(A_1164,k2_xboole_0(B_1165,C_1166)) = k3_xboole_0(A_1164,C_1166)
      | ~ r1_xboole_0(A_1164,B_1165) ) ),
    inference(cnfTransformation,[status(thm)],[f_698])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3829,plain,(
    ! [A_552,B_553] :
      ( r1_xboole_0(A_552,B_553)
      | k3_xboole_0(A_552,B_553) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_82])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_376,plain,(
    ! [A_261,B_262,C_263] : k2_xboole_0(k2_xboole_0(A_261,B_262),C_263) = k2_xboole_0(A_261,k2_xboole_0(B_262,C_263)) ),
    inference(cnfTransformation,[status(thm)],[f_520])).

tff(c_266,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_19','#skF_20'),'#skF_21'),'#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_511,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_19',k2_xboole_0('#skF_20','#skF_21')),'#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_266])).

tff(c_524,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_19',k2_xboole_0('#skF_21','#skF_20')),'#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_511])).

tff(c_3844,plain,(
    k3_xboole_0(k2_xboole_0('#skF_19',k2_xboole_0('#skF_21','#skF_20')),'#skF_22') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_3829,c_524])).

tff(c_3851,plain,(
    k3_xboole_0('#skF_22',k2_xboole_0('#skF_19',k2_xboole_0('#skF_21','#skF_20'))) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3844])).

tff(c_53296,plain,
    ( k3_xboole_0('#skF_22',k2_xboole_0('#skF_21','#skF_20')) != '#skF_9'
    | ~ r1_xboole_0('#skF_22','#skF_19') ),
    inference(superposition,[status(thm),theory(equality)],[c_53009,c_3851])).

tff(c_53498,plain,(
    k3_xboole_0('#skF_22',k2_xboole_0('#skF_21','#skF_20')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_53296])).

tff(c_53522,plain,
    ( k3_xboole_0('#skF_22','#skF_20') != '#skF_9'
    | ~ r1_xboole_0('#skF_22','#skF_21') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_53498])).

tff(c_53543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_1531,c_53522])).
%------------------------------------------------------------------------------
