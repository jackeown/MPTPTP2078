%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0084+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:13 EST 2020

% Result     : Theorem 12.32s
% Output     : CNFRefutation 12.32s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 101 expanded)
%              Number of leaves         :   50 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  97 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_19 > #skF_21 > #skF_9 > #skF_7 > #skF_20 > #skF_14 > #skF_22 > #skF_3 > #skF_2 > #skF_23 > #skF_8 > #skF_16 > #skF_15

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

tff('#skF_23',type,(
    '#skF_23': $i )).

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

tff(f_611,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_546,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_504,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_340,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_301,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_598,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_360,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_303,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

tff(c_386,plain,(
    ~ r1_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_611])).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_497,plain,(
    ! [A_314] :
      ( k1_xboole_0 = A_314
      | ~ v1_xboole_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_546])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_497])).

tff(c_348,plain,(
    ! [A_257] : r1_xboole_0(A_257,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_504])).

tff(c_514,plain,(
    ! [A_257] : r1_xboole_0(A_257,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_348])).

tff(c_726,plain,(
    ! [B_337,A_338] :
      ( r1_xboole_0(B_337,A_338)
      | ~ r1_xboole_0(A_338,B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_731,plain,(
    ! [A_257] : r1_xboole_0('#skF_9',A_257) ),
    inference(resolution,[status(thm)],[c_514,c_726])).

tff(c_246,plain,(
    ! [A_134,B_135] : k2_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = A_134 ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_1049,plain,(
    ! [B_366,A_367] : k2_xboole_0(B_366,A_367) = k2_xboole_0(A_367,B_366) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_224,plain,(
    ! [A_111,B_112] :
      ( k1_xboole_0 = A_111
      | k2_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_905,plain,(
    ! [A_111,B_112] :
      ( A_111 = '#skF_9'
      | k2_xboole_0(A_111,B_112) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_224])).

tff(c_1489,plain,(
    ! [B_384,A_385] :
      ( B_384 = '#skF_9'
      | k2_xboole_0(A_385,B_384) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_905])).

tff(c_1504,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = '#skF_9'
      | A_134 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1489])).

tff(c_9387,plain,(
    ! [A_571,B_572] :
      ( ~ r1_xboole_0(k3_xboole_0(A_571,B_572),B_572)
      | r1_xboole_0(A_571,B_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_598])).

tff(c_9422,plain,(
    ! [B_135,A_134] :
      ( ~ r1_xboole_0('#skF_9',B_135)
      | r1_xboole_0(A_134,B_135)
      | A_134 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_9387])).

tff(c_9482,plain,(
    ! [B_135] : r1_xboole_0('#skF_9',B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_9422])).

tff(c_384,plain,(
    r1_tarski('#skF_21','#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_611])).

tff(c_1512,plain,(
    ! [A_386,B_387] :
      ( k3_xboole_0(A_386,B_387) = A_386
      | ~ r1_tarski(A_386,B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_360])).

tff(c_1550,plain,(
    k3_xboole_0('#skF_21','#skF_23') = '#skF_21' ),
    inference(resolution,[status(thm)],[c_384,c_1512])).

tff(c_23392,plain,(
    ! [A_846,B_847,C_848] : k3_xboole_0(k3_xboole_0(A_846,B_847),C_848) = k3_xboole_0(A_846,k3_xboole_0(B_847,C_848)) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_23976,plain,(
    ! [C_849] : k3_xboole_0('#skF_21',k3_xboole_0('#skF_23',C_849)) = k3_xboole_0('#skF_21',C_849) ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_23392])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_382,plain,(
    r1_xboole_0('#skF_21',k3_xboole_0('#skF_22','#skF_23')) ),
    inference(cnfTransformation,[status(thm)],[f_611])).

tff(c_407,plain,(
    r1_xboole_0('#skF_21',k3_xboole_0('#skF_23','#skF_22')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_382])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2191,plain,(
    ! [A_408,B_409] :
      ( k3_xboole_0(A_408,B_409) = '#skF_9'
      | ~ r1_xboole_0(A_408,B_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_80])).

tff(c_2209,plain,(
    k3_xboole_0('#skF_21',k3_xboole_0('#skF_23','#skF_22')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_407,c_2191])).

tff(c_24106,plain,(
    k3_xboole_0('#skF_21','#skF_22') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_23976,c_2209])).

tff(c_378,plain,(
    ! [A_286,B_287] :
      ( ~ r1_xboole_0(k3_xboole_0(A_286,B_287),B_287)
      | r1_xboole_0(A_286,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_598])).

tff(c_24300,plain,
    ( ~ r1_xboole_0('#skF_9','#skF_22')
    | r1_xboole_0('#skF_21','#skF_22') ),
    inference(superposition,[status(thm),theory(equality)],[c_24106,c_378])).

tff(c_24418,plain,(
    r1_xboole_0('#skF_21','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9482,c_24300])).

tff(c_24420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_24418])).
%------------------------------------------------------------------------------
