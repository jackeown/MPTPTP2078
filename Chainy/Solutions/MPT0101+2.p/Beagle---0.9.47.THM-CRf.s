%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:14 EST 2020

% Result     : Theorem 24.82s
% Output     : CNFRefutation 24.82s
% Verified   : 
% Statistics : Number of formulae       :   74 (  84 expanded)
%              Number of leaves         :   48 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   32 (  40 expanded)
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

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_404,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_620,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

tff(f_641,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

tff(f_432,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_342,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_452,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

tff(f_687,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_694,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_288,plain,(
    ! [A_185,B_186] : k2_xboole_0(A_185,k4_xboole_0(B_186,A_185)) = k2_xboole_0(A_185,B_186) ),
    inference(cnfTransformation,[status(thm)],[f_404])).

tff(c_390,plain,(
    ! [A_300,B_301] : r1_xboole_0(k4_xboole_0(A_300,B_301),B_301) ),
    inference(cnfTransformation,[status(thm)],[f_620])).

tff(c_935,plain,(
    ! [B_397,A_398] :
      ( r1_xboole_0(B_397,A_398)
      | ~ r1_xboole_0(A_398,B_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_944,plain,(
    ! [B_301,A_300] : r1_xboole_0(B_301,k4_xboole_0(A_300,B_301)) ),
    inference(resolution,[status(thm)],[c_390,c_935])).

tff(c_1417,plain,(
    ! [A_426,B_427] :
      ( k4_xboole_0(A_426,B_427) = A_426
      | ~ r1_xboole_0(A_426,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_641])).

tff(c_1434,plain,(
    ! [B_301,A_300] : k4_xboole_0(B_301,k4_xboole_0(A_300,B_301)) = B_301 ),
    inference(resolution,[status(thm)],[c_944,c_1417])).

tff(c_64584,plain,(
    ! [A_1614,B_1615] : k4_xboole_0(k4_xboole_0(A_1614,B_1615),B_1615) = k4_xboole_0(A_1614,B_1615) ),
    inference(resolution,[status(thm)],[c_390,c_1417])).

tff(c_78,plain,(
    ! [A_38,B_39] : k2_xboole_0(k4_xboole_0(A_38,B_39),k4_xboole_0(B_39,A_38)) = k5_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64758,plain,(
    ! [B_1615,A_1614] : k2_xboole_0(k4_xboole_0(B_1615,k4_xboole_0(A_1614,B_1615)),k4_xboole_0(A_1614,B_1615)) = k5_xboole_0(B_1615,k4_xboole_0(A_1614,B_1615)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64584,c_78])).

tff(c_65046,plain,(
    ! [B_1615,A_1614] : k5_xboole_0(B_1615,k4_xboole_0(A_1614,B_1615)) = k2_xboole_0(B_1615,A_1614) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_1434,c_64758])).

tff(c_308,plain,(
    ! [A_207,B_208] : k4_xboole_0(A_207,k3_xboole_0(A_207,B_208)) = k4_xboole_0(A_207,B_208) ),
    inference(cnfTransformation,[status(thm)],[f_432])).

tff(c_248,plain,(
    ! [A_136,B_137] : k2_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = A_136 ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_328,plain,(
    ! [A_232,B_233] : k4_xboole_0(k2_xboole_0(A_232,B_233),k3_xboole_0(A_232,B_233)) = k2_xboole_0(k4_xboole_0(A_232,B_233),k4_xboole_0(B_233,A_232)) ),
    inference(cnfTransformation,[status(thm)],[f_452])).

tff(c_16406,plain,(
    ! [A_874,B_875] : k4_xboole_0(k2_xboole_0(A_874,B_875),k3_xboole_0(A_874,B_875)) = k5_xboole_0(A_874,B_875) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_328])).

tff(c_16642,plain,(
    ! [A_136,B_137] : k4_xboole_0(A_136,k3_xboole_0(A_136,k3_xboole_0(A_136,B_137))) = k5_xboole_0(A_136,k3_xboole_0(A_136,B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_16406])).

tff(c_16689,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = k4_xboole_0(A_136,B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_308,c_16642])).

tff(c_8,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,A_7) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_424,plain,(
    ! [A_339,B_340,C_341] : k5_xboole_0(k5_xboole_0(A_339,B_340),C_341) = k5_xboole_0(A_339,k5_xboole_0(B_340,C_341)) ),
    inference(cnfTransformation,[status(thm)],[f_687])).

tff(c_430,plain,(
    k5_xboole_0(k5_xboole_0('#skF_21','#skF_22'),k3_xboole_0('#skF_21','#skF_22')) != k2_xboole_0('#skF_21','#skF_22') ),
    inference(cnfTransformation,[status(thm)],[f_694])).

tff(c_433,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k3_xboole_0('#skF_21','#skF_22'))) != k2_xboole_0('#skF_21','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_430])).

tff(c_447,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k3_xboole_0('#skF_22','#skF_21'))) != k2_xboole_0('#skF_21','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_433])).

tff(c_448,plain,(
    k5_xboole_0('#skF_21',k5_xboole_0('#skF_22',k3_xboole_0('#skF_22','#skF_21'))) != k2_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_447])).

tff(c_47977,plain,(
    k5_xboole_0('#skF_21',k4_xboole_0('#skF_22','#skF_21')) != k2_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16689,c_448])).

tff(c_84356,plain,(
    k2_xboole_0('#skF_21','#skF_22') != k2_xboole_0('#skF_22','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65046,c_47977])).

tff(c_84360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_84356])).
%------------------------------------------------------------------------------
