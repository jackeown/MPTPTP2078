%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:36 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 915 expanded)
%              Number of leaves         :   23 ( 311 expanded)
%              Depth                    :   15
%              Number of atoms          :  247 (1229 expanded)
%              Number of equality atoms :  179 ( 748 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_20419,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_20423,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_20419])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_112,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_5311,plain,(
    ! [A_128,B_129,C_130] : k4_xboole_0(k4_xboole_0(A_128,B_129),C_130) = k4_xboole_0(A_128,k2_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5336,plain,(
    ! [A_128,B_129] : k4_xboole_0(A_128,k2_xboole_0(B_129,k1_xboole_0)) = k4_xboole_0(A_128,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_5311,c_12])).

tff(c_491,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_495,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_491])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_99,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_122,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_122])).

tff(c_141,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_268,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_329,plain,(
    ! [A_8,C_35] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,C_35)) = k4_xboole_0(A_8,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_268])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_113,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_117,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_322,plain,(
    ! [A_12,B_13,C_35] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_35)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_268])).

tff(c_939,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(A_49,k2_xboole_0(k3_xboole_0(A_49,B_50),C_51)) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_322])).

tff(c_993,plain,(
    ! [C_51] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_51)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_939])).

tff(c_1026,plain,(
    ! [C_51] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_51)) = k4_xboole_0('#skF_4',C_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_993])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_175,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_151])).

tff(c_183,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_175])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1678,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k4_xboole_0(A_62,B_63),k4_xboole_0(A_62,k2_xboole_0(B_63,C_64))) = k3_xboole_0(k4_xboole_0(A_62,B_63),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_18])).

tff(c_1834,plain,(
    ! [A_62,A_5] : k4_xboole_0(k4_xboole_0(A_62,A_5),k4_xboole_0(A_62,A_5)) = k3_xboole_0(k4_xboole_0(A_62,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1678])).

tff(c_1886,plain,(
    ! [A_65,A_66] : k3_xboole_0(k4_xboole_0(A_65,A_66),A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_1834])).

tff(c_1991,plain,(
    ! [C_67] : k3_xboole_0(k4_xboole_0('#skF_4',C_67),k2_xboole_0('#skF_5',C_67)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_1886])).

tff(c_2055,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_1991])).

tff(c_2090,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2055])).

tff(c_2092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_2090])).

tff(c_2093,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_2098,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2093,c_4])).

tff(c_2109,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_16])).

tff(c_2113,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2109])).

tff(c_333,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k1_xboole_0)) = k4_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_268])).

tff(c_2511,plain,(
    ! [A_77,C_78] : k4_xboole_0(A_77,k2_xboole_0(A_77,C_78)) = k4_xboole_0(k1_xboole_0,C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_268])).

tff(c_2562,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2511])).

tff(c_2571,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_2562])).

tff(c_302,plain,(
    ! [A_8,C_35] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_35)) = k4_xboole_0(k1_xboole_0,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_268])).

tff(c_2572,plain,(
    ! [A_8,C_35] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_35)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2571,c_302])).

tff(c_313,plain,(
    ! [A_33,B_34,B_15] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(k4_xboole_0(A_33,B_34),B_15))) = k3_xboole_0(k4_xboole_0(A_33,B_34),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_268])).

tff(c_4706,plain,(
    ! [A_115,B_116,B_117] : k4_xboole_0(A_115,k2_xboole_0(B_116,k4_xboole_0(A_115,k2_xboole_0(B_116,B_117)))) = k3_xboole_0(k4_xboole_0(A_115,B_116),B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_313])).

tff(c_4888,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_4706])).

tff(c_4963,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_2,c_4888])).

tff(c_289,plain,(
    ! [A_33,B_34,B_13] : k4_xboole_0(A_33,k2_xboole_0(B_34,k3_xboole_0(k4_xboole_0(A_33,B_34),B_13))) = k4_xboole_0(k4_xboole_0(A_33,B_34),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_16])).

tff(c_337,plain,(
    ! [A_33,B_34,B_13] : k4_xboole_0(A_33,k2_xboole_0(B_34,k3_xboole_0(k4_xboole_0(A_33,B_34),B_13))) = k4_xboole_0(A_33,k2_xboole_0(B_34,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_289])).

tff(c_5130,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4963,c_337])).

tff(c_5145,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_333,c_5130])).

tff(c_5151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5145,c_4963])).

tff(c_5153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_5151])).

tff(c_5154,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_5164,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5154,c_4])).

tff(c_5188,plain,(
    ! [A_122,B_123] : k4_xboole_0(A_122,k3_xboole_0(A_122,B_123)) = k4_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5200,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5164,c_5188])).

tff(c_5210,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5200])).

tff(c_5169,plain,(
    ! [A_120,B_121] : k4_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5178,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5169])).

tff(c_5879,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5178])).

tff(c_5184,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5169])).

tff(c_5187,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5184])).

tff(c_6269,plain,(
    ! [A_151,C_152] : k4_xboole_0(A_151,k2_xboole_0(A_151,C_152)) = k4_xboole_0(k1_xboole_0,C_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_5187,c_5311])).

tff(c_6355,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6269])).

tff(c_6370,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5187,c_6355])).

tff(c_5351,plain,(
    ! [A_8,C_130] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_130)) = k4_xboole_0(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_5187,c_5311])).

tff(c_6732,plain,(
    ! [A_158,C_159] : k4_xboole_0(A_158,k2_xboole_0(A_158,C_159)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6370,c_5351])).

tff(c_6825,plain,(
    ! [B_160,A_161] : k4_xboole_0(B_160,k2_xboole_0(A_161,B_160)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6732])).

tff(c_5365,plain,(
    ! [A_14,B_15,C_130] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_130)) = k4_xboole_0(k3_xboole_0(A_14,B_15),C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5311])).

tff(c_7311,plain,(
    ! [B_170,B_171] : k4_xboole_0(k3_xboole_0(B_170,B_171),B_170) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6825,c_5365])).

tff(c_7360,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5879,c_7311])).

tff(c_8409,plain,(
    ! [A_184,B_185,C_186] : k4_xboole_0(k4_xboole_0(A_184,B_185),k4_xboole_0(A_184,k2_xboole_0(B_185,C_186))) = k3_xboole_0(k4_xboole_0(A_184,B_185),C_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_5311,c_18])).

tff(c_8592,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5210,c_8409])).

tff(c_8675,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7360,c_8592])).

tff(c_5325,plain,(
    ! [A_128,B_129,B_13] : k4_xboole_0(A_128,k2_xboole_0(B_129,k3_xboole_0(k4_xboole_0(A_128,B_129),B_13))) = k4_xboole_0(k4_xboole_0(A_128,B_129),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_5311,c_16])).

tff(c_5379,plain,(
    ! [A_128,B_129,B_13] : k4_xboole_0(A_128,k2_xboole_0(B_129,k3_xboole_0(k4_xboole_0(A_128,B_129),B_13))) = k4_xboole_0(A_128,k2_xboole_0(B_129,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5325])).

tff(c_9165,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8675,c_5379])).

tff(c_9180,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5336,c_5210,c_9165])).

tff(c_9186,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_8675])).

tff(c_9188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_9186])).

tff(c_9189,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_9199,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9189])).

tff(c_9203,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_9199])).

tff(c_9204,plain,(
    ! [A_192,B_193] : k4_xboole_0(A_192,k4_xboole_0(A_192,B_193)) = k3_xboole_0(A_192,B_193) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9219,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_9204])).

tff(c_9222,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9219])).

tff(c_9190,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_9194,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9190,c_4])).

tff(c_19110,plain,(
    ! [A_344,B_345] : k4_xboole_0(A_344,k3_xboole_0(A_344,B_345)) = k4_xboole_0(A_344,B_345) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19125,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9194,c_19110])).

tff(c_19136,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19125])).

tff(c_19214,plain,(
    ! [A_348,B_349,C_350] : k4_xboole_0(k4_xboole_0(A_348,B_349),C_350) = k4_xboole_0(A_348,k2_xboole_0(B_349,C_350)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19522,plain,(
    ! [C_357] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_357)) = k4_xboole_0('#skF_1',C_357) ),
    inference(superposition,[status(thm),theory(equality)],[c_19136,c_19214])).

tff(c_20182,plain,(
    ! [B_375] : k4_xboole_0('#skF_1',k2_xboole_0(B_375,'#skF_2')) = k4_xboole_0('#skF_1',B_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19522])).

tff(c_9265,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_9269,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9265,c_4])).

tff(c_9274,plain,(
    ! [A_196,B_197] : k4_xboole_0(A_196,k3_xboole_0(A_196,B_197)) = k4_xboole_0(A_196,B_197) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9295,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_9274])).

tff(c_9305,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9295])).

tff(c_9377,plain,(
    ! [A_200,B_201,C_202] : k4_xboole_0(k4_xboole_0(A_200,B_201),C_202) = k4_xboole_0(A_200,k2_xboole_0(B_201,C_202)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15715,plain,(
    ! [A_292,B_293,C_294] : k4_xboole_0(k4_xboole_0(A_292,B_293),k4_xboole_0(A_292,k2_xboole_0(B_293,C_294))) = k3_xboole_0(k4_xboole_0(A_292,B_293),C_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_9377,c_18])).

tff(c_15956,plain,(
    ! [C_294] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_294))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_9305,c_15715])).

tff(c_16058,plain,(
    ! [C_294] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_294)) = k3_xboole_0('#skF_4',C_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_18,c_15956])).

tff(c_9331,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_9335,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_9331])).

tff(c_16749,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16058,c_9335])).

tff(c_16752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9269,c_16749])).

tff(c_16753,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_16758,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16753,c_4])).

tff(c_16766,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16758,c_16])).

tff(c_16769,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16766])).

tff(c_16846,plain,(
    ! [A_303,B_304,C_305] : k4_xboole_0(k4_xboole_0(A_303,B_304),C_305) = k4_xboole_0(A_303,k2_xboole_0(B_304,C_305)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17819,plain,(
    ! [A_323,C_324] : k4_xboole_0(A_323,k2_xboole_0(A_323,C_324)) = k4_xboole_0(k1_xboole_0,C_324) ),
    inference(superposition,[status(thm),theory(equality)],[c_9222,c_16846])).

tff(c_17911,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_17819])).

tff(c_17926,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9222,c_17911])).

tff(c_16902,plain,(
    ! [A_8,C_305] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_305)) = k4_xboole_0(k1_xboole_0,C_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_9222,c_16846])).

tff(c_17927,plain,(
    ! [A_8,C_305] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_305)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17926,c_16902])).

tff(c_16913,plain,(
    ! [A_303,B_304,B_15] : k4_xboole_0(A_303,k2_xboole_0(B_304,k4_xboole_0(k4_xboole_0(A_303,B_304),B_15))) = k3_xboole_0(k4_xboole_0(A_303,B_304),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16846])).

tff(c_18703,plain,(
    ! [A_339,B_340,B_341] : k4_xboole_0(A_339,k2_xboole_0(B_340,k4_xboole_0(A_339,k2_xboole_0(B_340,B_341)))) = k3_xboole_0(k4_xboole_0(A_339,B_340),B_341) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16913])).

tff(c_18876,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16769,c_18703])).

tff(c_18933,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17927,c_2,c_18876])).

tff(c_19063,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18933,c_16])).

tff(c_19068,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16769,c_14,c_12,c_19063])).

tff(c_16860,plain,(
    ! [A_303,B_304] : k4_xboole_0(A_303,k2_xboole_0(B_304,k4_xboole_0(A_303,B_304))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16846,c_9222])).

tff(c_18889,plain,(
    ! [A_339,A_5] : k4_xboole_0(A_339,k2_xboole_0(A_5,k4_xboole_0(A_339,A_5))) = k3_xboole_0(k4_xboole_0(A_339,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_18703])).

tff(c_18935,plain,(
    ! [A_339,A_5] : k3_xboole_0(k4_xboole_0(A_339,A_5),A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_18889])).

tff(c_19075,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19068,c_18935])).

tff(c_19094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9203,c_19075])).

tff(c_19095,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_19109,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19095,c_4])).

tff(c_19158,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_19109,c_16])).

tff(c_19161,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19158])).

tff(c_20206,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_20182,c_19161])).

tff(c_20263,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20206,c_18])).

tff(c_20267,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9222,c_20263])).

tff(c_20269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9203,c_20267])).

tff(c_20270,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_9189])).

tff(c_20275,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20270,c_4])).

tff(c_20347,plain,(
    ! [A_380,B_381] : k4_xboole_0(A_380,k3_xboole_0(A_380,B_381)) = k4_xboole_0(A_380,B_381) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20365,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20275,c_20347])).

tff(c_20380,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20365])).

tff(c_20471,plain,(
    ! [A_384,B_385,C_386] : k4_xboole_0(k4_xboole_0(A_384,B_385),C_386) = k4_xboole_0(A_384,k2_xboole_0(B_385,C_386)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20538,plain,(
    ! [A_8,C_386] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,C_386)) = k4_xboole_0(A_8,C_386) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20471])).

tff(c_20517,plain,(
    ! [A_12,B_13,C_386] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_386)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_386) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_20471])).

tff(c_21696,plain,(
    ! [A_410,B_411,C_412] : k4_xboole_0(A_410,k2_xboole_0(k3_xboole_0(A_410,B_411),C_412)) = k4_xboole_0(A_410,k2_xboole_0(B_411,C_412)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20517])).

tff(c_21783,plain,(
    ! [C_412] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_412)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_412)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_21696])).

tff(c_21824,plain,(
    ! [C_412] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_412)) = k4_xboole_0('#skF_4',C_412) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20538,c_21783])).

tff(c_20288,plain,(
    ! [A_376,B_377] : k4_xboole_0(A_376,k4_xboole_0(A_376,B_377)) = k3_xboole_0(A_376,B_377) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20303,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20288])).

tff(c_20306,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20303])).

tff(c_20528,plain,(
    ! [A_384,B_385] : k4_xboole_0(A_384,k2_xboole_0(B_385,k4_xboole_0(A_384,B_385))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20306,c_20471])).

tff(c_20492,plain,(
    ! [A_384,B_385,B_15] : k4_xboole_0(A_384,k2_xboole_0(B_385,k4_xboole_0(k4_xboole_0(A_384,B_385),B_15))) = k3_xboole_0(k4_xboole_0(A_384,B_385),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_20471,c_18])).

tff(c_23158,plain,(
    ! [A_432,B_433,B_434] : k4_xboole_0(A_432,k2_xboole_0(B_433,k4_xboole_0(A_432,k2_xboole_0(B_433,B_434)))) = k3_xboole_0(k4_xboole_0(A_432,B_433),B_434) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20492])).

tff(c_23340,plain,(
    ! [A_432,A_5] : k4_xboole_0(A_432,k2_xboole_0(A_5,k4_xboole_0(A_432,A_5))) = k3_xboole_0(k4_xboole_0(A_432,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_23158])).

tff(c_23387,plain,(
    ! [A_435,A_436] : k3_xboole_0(k4_xboole_0(A_435,A_436),A_436) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20528,c_23340])).

tff(c_25204,plain,(
    ! [C_456] : k3_xboole_0(k4_xboole_0('#skF_4',C_456),k2_xboole_0('#skF_6',C_456)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21824,c_23387])).

tff(c_25292,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20380,c_25204])).

tff(c_25337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20423,c_25292])).

tff(c_25339,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_20271,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_9189])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_25569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25339,c_9190,c_20271,c_32])).

tff(c_25571,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25676,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_25571,c_22])).

tff(c_25677,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_25676])).

tff(c_25681,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_25677])).

tff(c_25584,plain,(
    ! [A_464,B_465] : k4_xboole_0(A_464,k4_xboole_0(A_464,B_465)) = k3_xboole_0(A_464,B_465) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25599,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25584])).

tff(c_25602,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_25599])).

tff(c_25570,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_25579,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25570,c_4])).

tff(c_25603,plain,(
    ! [A_466,B_467] : k4_xboole_0(A_466,k3_xboole_0(A_466,B_467)) = k4_xboole_0(A_466,B_467) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25615,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25579,c_25603])).

tff(c_25622,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25615])).

tff(c_25717,plain,(
    ! [A_472,B_473,C_474] : k4_xboole_0(k4_xboole_0(A_472,B_473),C_474) = k4_xboole_0(A_472,k2_xboole_0(B_473,C_474)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25720,plain,(
    ! [A_472,B_473,C_474,C_11] : k4_xboole_0(k4_xboole_0(A_472,k2_xboole_0(B_473,C_474)),C_11) = k4_xboole_0(k4_xboole_0(A_472,B_473),k2_xboole_0(C_474,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25717,c_14])).

tff(c_27798,plain,(
    ! [A_518,B_519,C_520,C_521] : k4_xboole_0(A_518,k2_xboole_0(k2_xboole_0(B_519,C_520),C_521)) = k4_xboole_0(A_518,k2_xboole_0(B_519,k2_xboole_0(C_520,C_521))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_25720])).

tff(c_25751,plain,(
    ! [C_474] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_474)) = k4_xboole_0('#skF_1',C_474) ),
    inference(superposition,[status(thm),theory(equality)],[c_25622,c_25717])).

tff(c_28126,plain,(
    ! [C_524] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_524))) = k4_xboole_0('#skF_1',C_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_27798,c_25751])).

tff(c_28165,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_28126])).

tff(c_28175,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25622,c_28165])).

tff(c_28197,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_18])).

tff(c_28205,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25602,c_28197])).

tff(c_28207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25681,c_28205])).

tff(c_28208,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_25676])).

tff(c_28213,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_28208])).

tff(c_28209,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_25676])).

tff(c_28217,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28209,c_4])).

tff(c_28221,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28217,c_16])).

tff(c_28224,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28221])).

tff(c_28275,plain,(
    ! [A_527,B_528,C_529] : k4_xboole_0(k4_xboole_0(A_527,B_528),C_529) = k4_xboole_0(A_527,k2_xboole_0(B_528,C_529)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28585,plain,(
    ! [C_536] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_536)) = k4_xboole_0('#skF_1',C_536) ),
    inference(superposition,[status(thm),theory(equality)],[c_28224,c_28275])).

tff(c_29640,plain,(
    ! [A_555] : k4_xboole_0('#skF_1',k2_xboole_0(A_555,'#skF_2')) = k4_xboole_0('#skF_1',A_555) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_28585])).

tff(c_29678,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_29640,c_25622])).

tff(c_29754,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29678,c_18])).

tff(c_29760,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25602,c_29754])).

tff(c_29762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28213,c_29760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.68  
% 9.02/3.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.68  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.02/3.68  
% 9.02/3.68  %Foreground sorts:
% 9.02/3.68  
% 9.02/3.68  
% 9.02/3.68  %Background operators:
% 9.02/3.68  
% 9.02/3.68  
% 9.02/3.68  %Foreground operators:
% 9.02/3.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.02/3.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.02/3.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.02/3.68  tff('#skF_5', type, '#skF_5': $i).
% 9.02/3.68  tff('#skF_6', type, '#skF_6': $i).
% 9.02/3.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.02/3.68  tff('#skF_2', type, '#skF_2': $i).
% 9.02/3.68  tff('#skF_3', type, '#skF_3': $i).
% 9.02/3.68  tff('#skF_1', type, '#skF_1': $i).
% 9.02/3.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.02/3.68  tff('#skF_4', type, '#skF_4': $i).
% 9.02/3.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.02/3.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.02/3.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.02/3.68  
% 9.02/3.71  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.02/3.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.02/3.71  tff(f_60, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 9.02/3.71  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.02/3.71  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.02/3.71  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.02/3.71  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.02/3.71  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.02/3.71  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.02/3.71  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.02/3.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.02/3.71  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_33, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 9.02/3.71  tff(c_20419, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_20423, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_20419])).
% 9.02/3.71  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.02/3.71  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_108, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 9.02/3.71  tff(c_112, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_108])).
% 9.02/3.71  tff(c_5311, plain, (![A_128, B_129, C_130]: (k4_xboole_0(k4_xboole_0(A_128, B_129), C_130)=k4_xboole_0(A_128, k2_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_5336, plain, (![A_128, B_129]: (k4_xboole_0(A_128, k2_xboole_0(B_129, k1_xboole_0))=k4_xboole_0(A_128, B_129))), inference(superposition, [status(thm), theory('equality')], [c_5311, c_12])).
% 9.02/3.71  tff(c_491, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_495, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_491])).
% 9.02/3.71  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 9.02/3.71  tff(c_99, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 9.02/3.71  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.02/3.71  tff(c_103, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_4])).
% 9.02/3.71  tff(c_122, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_134, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_103, c_122])).
% 9.02/3.71  tff(c_141, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_134])).
% 9.02/3.71  tff(c_268, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_329, plain, (![A_8, C_35]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, C_35))=k4_xboole_0(A_8, C_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_268])).
% 9.02/3.71  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_31, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 9.02/3.71  tff(c_113, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 9.02/3.71  tff(c_117, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_4])).
% 9.02/3.71  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_322, plain, (![A_12, B_13, C_35]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_35))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_35))), inference(superposition, [status(thm), theory('equality')], [c_16, c_268])).
% 9.02/3.71  tff(c_939, plain, (![A_49, B_50, C_51]: (k4_xboole_0(A_49, k2_xboole_0(k3_xboole_0(A_49, B_50), C_51))=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_322])).
% 9.02/3.71  tff(c_993, plain, (![C_51]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_51))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_51)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_939])).
% 9.02/3.71  tff(c_1026, plain, (![C_51]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_51))=k4_xboole_0('#skF_4', C_51))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_993])).
% 9.02/3.71  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.02/3.71  tff(c_151, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_175, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_151])).
% 9.02/3.71  tff(c_183, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_175])).
% 9.02/3.71  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.02/3.71  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_1678, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k4_xboole_0(A_62, B_63), k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)))=k3_xboole_0(k4_xboole_0(A_62, B_63), C_64))), inference(superposition, [status(thm), theory('equality')], [c_268, c_18])).
% 9.02/3.71  tff(c_1834, plain, (![A_62, A_5]: (k4_xboole_0(k4_xboole_0(A_62, A_5), k4_xboole_0(A_62, A_5))=k3_xboole_0(k4_xboole_0(A_62, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1678])).
% 9.02/3.71  tff(c_1886, plain, (![A_65, A_66]: (k3_xboole_0(k4_xboole_0(A_65, A_66), A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_1834])).
% 9.02/3.71  tff(c_1991, plain, (![C_67]: (k3_xboole_0(k4_xboole_0('#skF_4', C_67), k2_xboole_0('#skF_5', C_67))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1026, c_1886])).
% 9.02/3.71  tff(c_2055, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_141, c_1991])).
% 9.02/3.71  tff(c_2090, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2055])).
% 9.02/3.71  tff(c_2092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_2090])).
% 9.02/3.71  tff(c_2093, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_2098, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2093, c_4])).
% 9.02/3.71  tff(c_2109, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2098, c_16])).
% 9.02/3.71  tff(c_2113, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2109])).
% 9.02/3.71  tff(c_333, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k1_xboole_0))=k4_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_12, c_268])).
% 9.02/3.71  tff(c_2511, plain, (![A_77, C_78]: (k4_xboole_0(A_77, k2_xboole_0(A_77, C_78))=k4_xboole_0(k1_xboole_0, C_78))), inference(superposition, [status(thm), theory('equality')], [c_183, c_268])).
% 9.02/3.71  tff(c_2562, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2511])).
% 9.02/3.71  tff(c_2571, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_2562])).
% 9.02/3.71  tff(c_302, plain, (![A_8, C_35]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_35))=k4_xboole_0(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_183, c_268])).
% 9.02/3.71  tff(c_2572, plain, (![A_8, C_35]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_35))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2571, c_302])).
% 9.02/3.71  tff(c_313, plain, (![A_33, B_34, B_15]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(k4_xboole_0(A_33, B_34), B_15)))=k3_xboole_0(k4_xboole_0(A_33, B_34), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_268])).
% 9.02/3.71  tff(c_4706, plain, (![A_115, B_116, B_117]: (k4_xboole_0(A_115, k2_xboole_0(B_116, k4_xboole_0(A_115, k2_xboole_0(B_116, B_117))))=k3_xboole_0(k4_xboole_0(A_115, B_116), B_117))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_313])).
% 9.02/3.71  tff(c_4888, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2113, c_4706])).
% 9.02/3.71  tff(c_4963, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_2, c_4888])).
% 9.02/3.71  tff(c_289, plain, (![A_33, B_34, B_13]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k3_xboole_0(k4_xboole_0(A_33, B_34), B_13)))=k4_xboole_0(k4_xboole_0(A_33, B_34), B_13))), inference(superposition, [status(thm), theory('equality')], [c_268, c_16])).
% 9.02/3.71  tff(c_337, plain, (![A_33, B_34, B_13]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k3_xboole_0(k4_xboole_0(A_33, B_34), B_13)))=k4_xboole_0(A_33, k2_xboole_0(B_34, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_289])).
% 9.02/3.71  tff(c_5130, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4963, c_337])).
% 9.02/3.71  tff(c_5145, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_333, c_5130])).
% 9.02/3.71  tff(c_5151, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5145, c_4963])).
% 9.02/3.71  tff(c_5153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_5151])).
% 9.02/3.71  tff(c_5154, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 9.02/3.71  tff(c_5164, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5154, c_4])).
% 9.02/3.71  tff(c_5188, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k3_xboole_0(A_122, B_123))=k4_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_5200, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5164, c_5188])).
% 9.02/3.71  tff(c_5210, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5200])).
% 9.02/3.71  tff(c_5169, plain, (![A_120, B_121]: (k4_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_5178, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5169])).
% 9.02/3.71  tff(c_5879, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5178])).
% 9.02/3.71  tff(c_5184, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5169])).
% 9.02/3.71  tff(c_5187, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5184])).
% 9.02/3.71  tff(c_6269, plain, (![A_151, C_152]: (k4_xboole_0(A_151, k2_xboole_0(A_151, C_152))=k4_xboole_0(k1_xboole_0, C_152))), inference(superposition, [status(thm), theory('equality')], [c_5187, c_5311])).
% 9.02/3.71  tff(c_6355, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_6269])).
% 9.02/3.71  tff(c_6370, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5187, c_6355])).
% 9.02/3.71  tff(c_5351, plain, (![A_8, C_130]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_130))=k4_xboole_0(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_5187, c_5311])).
% 9.02/3.71  tff(c_6732, plain, (![A_158, C_159]: (k4_xboole_0(A_158, k2_xboole_0(A_158, C_159))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6370, c_5351])).
% 9.02/3.71  tff(c_6825, plain, (![B_160, A_161]: (k4_xboole_0(B_160, k2_xboole_0(A_161, B_160))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6732])).
% 9.02/3.71  tff(c_5365, plain, (![A_14, B_15, C_130]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_130))=k4_xboole_0(k3_xboole_0(A_14, B_15), C_130))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5311])).
% 9.02/3.71  tff(c_7311, plain, (![B_170, B_171]: (k4_xboole_0(k3_xboole_0(B_170, B_171), B_170)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6825, c_5365])).
% 9.02/3.71  tff(c_7360, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5879, c_7311])).
% 9.02/3.71  tff(c_8409, plain, (![A_184, B_185, C_186]: (k4_xboole_0(k4_xboole_0(A_184, B_185), k4_xboole_0(A_184, k2_xboole_0(B_185, C_186)))=k3_xboole_0(k4_xboole_0(A_184, B_185), C_186))), inference(superposition, [status(thm), theory('equality')], [c_5311, c_18])).
% 9.02/3.71  tff(c_8592, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5210, c_8409])).
% 9.02/3.71  tff(c_8675, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7360, c_8592])).
% 9.02/3.71  tff(c_5325, plain, (![A_128, B_129, B_13]: (k4_xboole_0(A_128, k2_xboole_0(B_129, k3_xboole_0(k4_xboole_0(A_128, B_129), B_13)))=k4_xboole_0(k4_xboole_0(A_128, B_129), B_13))), inference(superposition, [status(thm), theory('equality')], [c_5311, c_16])).
% 9.02/3.71  tff(c_5379, plain, (![A_128, B_129, B_13]: (k4_xboole_0(A_128, k2_xboole_0(B_129, k3_xboole_0(k4_xboole_0(A_128, B_129), B_13)))=k4_xboole_0(A_128, k2_xboole_0(B_129, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5325])).
% 9.02/3.71  tff(c_9165, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8675, c_5379])).
% 9.02/3.71  tff(c_9180, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5336, c_5210, c_9165])).
% 9.02/3.71  tff(c_9186, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_8675])).
% 9.02/3.71  tff(c_9188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_9186])).
% 9.02/3.71  tff(c_9189, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 9.02/3.71  tff(c_9199, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_9189])).
% 9.02/3.71  tff(c_9203, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_9199])).
% 9.02/3.71  tff(c_9204, plain, (![A_192, B_193]: (k4_xboole_0(A_192, k4_xboole_0(A_192, B_193))=k3_xboole_0(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_9219, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_9204])).
% 9.02/3.71  tff(c_9222, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9219])).
% 9.02/3.71  tff(c_9190, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 9.02/3.71  tff(c_9194, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_9190, c_4])).
% 9.02/3.71  tff(c_19110, plain, (![A_344, B_345]: (k4_xboole_0(A_344, k3_xboole_0(A_344, B_345))=k4_xboole_0(A_344, B_345))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_19125, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9194, c_19110])).
% 9.02/3.71  tff(c_19136, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19125])).
% 9.02/3.71  tff(c_19214, plain, (![A_348, B_349, C_350]: (k4_xboole_0(k4_xboole_0(A_348, B_349), C_350)=k4_xboole_0(A_348, k2_xboole_0(B_349, C_350)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_19522, plain, (![C_357]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_357))=k4_xboole_0('#skF_1', C_357))), inference(superposition, [status(thm), theory('equality')], [c_19136, c_19214])).
% 9.02/3.71  tff(c_20182, plain, (![B_375]: (k4_xboole_0('#skF_1', k2_xboole_0(B_375, '#skF_2'))=k4_xboole_0('#skF_1', B_375))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19522])).
% 9.02/3.71  tff(c_9265, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 9.02/3.71  tff(c_9269, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_9265, c_4])).
% 9.02/3.71  tff(c_9274, plain, (![A_196, B_197]: (k4_xboole_0(A_196, k3_xboole_0(A_196, B_197))=k4_xboole_0(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_9295, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_103, c_9274])).
% 9.02/3.71  tff(c_9305, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9295])).
% 9.02/3.71  tff(c_9377, plain, (![A_200, B_201, C_202]: (k4_xboole_0(k4_xboole_0(A_200, B_201), C_202)=k4_xboole_0(A_200, k2_xboole_0(B_201, C_202)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_15715, plain, (![A_292, B_293, C_294]: (k4_xboole_0(k4_xboole_0(A_292, B_293), k4_xboole_0(A_292, k2_xboole_0(B_293, C_294)))=k3_xboole_0(k4_xboole_0(A_292, B_293), C_294))), inference(superposition, [status(thm), theory('equality')], [c_9377, c_18])).
% 9.02/3.71  tff(c_15956, plain, (![C_294]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_294)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_294))), inference(superposition, [status(thm), theory('equality')], [c_9305, c_15715])).
% 9.02/3.71  tff(c_16058, plain, (![C_294]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_294))=k3_xboole_0('#skF_4', C_294))), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_18, c_15956])).
% 9.02/3.71  tff(c_9331, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_9335, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_9331])).
% 9.02/3.71  tff(c_16749, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16058, c_9335])).
% 9.02/3.71  tff(c_16752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9269, c_16749])).
% 9.02/3.71  tff(c_16753, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_16758, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16753, c_4])).
% 9.02/3.71  tff(c_16766, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16758, c_16])).
% 9.02/3.71  tff(c_16769, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16766])).
% 9.02/3.71  tff(c_16846, plain, (![A_303, B_304, C_305]: (k4_xboole_0(k4_xboole_0(A_303, B_304), C_305)=k4_xboole_0(A_303, k2_xboole_0(B_304, C_305)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_17819, plain, (![A_323, C_324]: (k4_xboole_0(A_323, k2_xboole_0(A_323, C_324))=k4_xboole_0(k1_xboole_0, C_324))), inference(superposition, [status(thm), theory('equality')], [c_9222, c_16846])).
% 9.02/3.71  tff(c_17911, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_17819])).
% 9.02/3.71  tff(c_17926, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9222, c_17911])).
% 9.02/3.71  tff(c_16902, plain, (![A_8, C_305]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_305))=k4_xboole_0(k1_xboole_0, C_305))), inference(superposition, [status(thm), theory('equality')], [c_9222, c_16846])).
% 9.02/3.71  tff(c_17927, plain, (![A_8, C_305]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_305))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17926, c_16902])).
% 9.02/3.71  tff(c_16913, plain, (![A_303, B_304, B_15]: (k4_xboole_0(A_303, k2_xboole_0(B_304, k4_xboole_0(k4_xboole_0(A_303, B_304), B_15)))=k3_xboole_0(k4_xboole_0(A_303, B_304), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16846])).
% 9.02/3.71  tff(c_18703, plain, (![A_339, B_340, B_341]: (k4_xboole_0(A_339, k2_xboole_0(B_340, k4_xboole_0(A_339, k2_xboole_0(B_340, B_341))))=k3_xboole_0(k4_xboole_0(A_339, B_340), B_341))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16913])).
% 9.02/3.71  tff(c_18876, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16769, c_18703])).
% 9.02/3.71  tff(c_18933, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17927, c_2, c_18876])).
% 9.02/3.71  tff(c_19063, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18933, c_16])).
% 9.02/3.71  tff(c_19068, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16769, c_14, c_12, c_19063])).
% 9.02/3.71  tff(c_16860, plain, (![A_303, B_304]: (k4_xboole_0(A_303, k2_xboole_0(B_304, k4_xboole_0(A_303, B_304)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16846, c_9222])).
% 9.02/3.71  tff(c_18889, plain, (![A_339, A_5]: (k4_xboole_0(A_339, k2_xboole_0(A_5, k4_xboole_0(A_339, A_5)))=k3_xboole_0(k4_xboole_0(A_339, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_18703])).
% 9.02/3.71  tff(c_18935, plain, (![A_339, A_5]: (k3_xboole_0(k4_xboole_0(A_339, A_5), A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_18889])).
% 9.02/3.71  tff(c_19075, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19068, c_18935])).
% 9.02/3.71  tff(c_19094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9203, c_19075])).
% 9.02/3.71  tff(c_19095, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 9.02/3.71  tff(c_19109, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_19095, c_4])).
% 9.02/3.71  tff(c_19158, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_19109, c_16])).
% 9.02/3.71  tff(c_19161, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19158])).
% 9.02/3.71  tff(c_20206, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_20182, c_19161])).
% 9.02/3.71  tff(c_20263, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20206, c_18])).
% 9.02/3.71  tff(c_20267, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9222, c_20263])).
% 9.02/3.71  tff(c_20269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9203, c_20267])).
% 9.02/3.71  tff(c_20270, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_9189])).
% 9.02/3.71  tff(c_20275, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_20270, c_4])).
% 9.02/3.71  tff(c_20347, plain, (![A_380, B_381]: (k4_xboole_0(A_380, k3_xboole_0(A_380, B_381))=k4_xboole_0(A_380, B_381))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_20365, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20275, c_20347])).
% 9.02/3.71  tff(c_20380, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20365])).
% 9.02/3.71  tff(c_20471, plain, (![A_384, B_385, C_386]: (k4_xboole_0(k4_xboole_0(A_384, B_385), C_386)=k4_xboole_0(A_384, k2_xboole_0(B_385, C_386)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_20538, plain, (![A_8, C_386]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, C_386))=k4_xboole_0(A_8, C_386))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20471])).
% 9.02/3.71  tff(c_20517, plain, (![A_12, B_13, C_386]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_386))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_386))), inference(superposition, [status(thm), theory('equality')], [c_16, c_20471])).
% 9.02/3.71  tff(c_21696, plain, (![A_410, B_411, C_412]: (k4_xboole_0(A_410, k2_xboole_0(k3_xboole_0(A_410, B_411), C_412))=k4_xboole_0(A_410, k2_xboole_0(B_411, C_412)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20517])).
% 9.02/3.71  tff(c_21783, plain, (![C_412]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_412))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_412)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_21696])).
% 9.02/3.71  tff(c_21824, plain, (![C_412]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_412))=k4_xboole_0('#skF_4', C_412))), inference(demodulation, [status(thm), theory('equality')], [c_20538, c_21783])).
% 9.02/3.71  tff(c_20288, plain, (![A_376, B_377]: (k4_xboole_0(A_376, k4_xboole_0(A_376, B_377))=k3_xboole_0(A_376, B_377))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_20303, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20288])).
% 9.02/3.71  tff(c_20306, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20303])).
% 9.02/3.71  tff(c_20528, plain, (![A_384, B_385]: (k4_xboole_0(A_384, k2_xboole_0(B_385, k4_xboole_0(A_384, B_385)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20306, c_20471])).
% 9.02/3.71  tff(c_20492, plain, (![A_384, B_385, B_15]: (k4_xboole_0(A_384, k2_xboole_0(B_385, k4_xboole_0(k4_xboole_0(A_384, B_385), B_15)))=k3_xboole_0(k4_xboole_0(A_384, B_385), B_15))), inference(superposition, [status(thm), theory('equality')], [c_20471, c_18])).
% 9.02/3.71  tff(c_23158, plain, (![A_432, B_433, B_434]: (k4_xboole_0(A_432, k2_xboole_0(B_433, k4_xboole_0(A_432, k2_xboole_0(B_433, B_434))))=k3_xboole_0(k4_xboole_0(A_432, B_433), B_434))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20492])).
% 9.02/3.71  tff(c_23340, plain, (![A_432, A_5]: (k4_xboole_0(A_432, k2_xboole_0(A_5, k4_xboole_0(A_432, A_5)))=k3_xboole_0(k4_xboole_0(A_432, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_23158])).
% 9.02/3.71  tff(c_23387, plain, (![A_435, A_436]: (k3_xboole_0(k4_xboole_0(A_435, A_436), A_436)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20528, c_23340])).
% 9.02/3.71  tff(c_25204, plain, (![C_456]: (k3_xboole_0(k4_xboole_0('#skF_4', C_456), k2_xboole_0('#skF_6', C_456))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21824, c_23387])).
% 9.02/3.71  tff(c_25292, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20380, c_25204])).
% 9.02/3.71  tff(c_25337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20423, c_25292])).
% 9.02/3.71  tff(c_25339, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_33])).
% 9.02/3.71  tff(c_20271, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_9189])).
% 9.02/3.71  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 9.02/3.71  tff(c_25569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25339, c_9190, c_20271, c_32])).
% 9.02/3.71  tff(c_25571, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 9.02/3.71  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.02/3.71  tff(c_25676, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_25571, c_22])).
% 9.02/3.71  tff(c_25677, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_25676])).
% 9.02/3.71  tff(c_25681, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_25677])).
% 9.02/3.71  tff(c_25584, plain, (![A_464, B_465]: (k4_xboole_0(A_464, k4_xboole_0(A_464, B_465))=k3_xboole_0(A_464, B_465))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.02/3.71  tff(c_25599, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25584])).
% 9.02/3.71  tff(c_25602, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_25599])).
% 9.02/3.71  tff(c_25570, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 9.02/3.71  tff(c_25579, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25570, c_4])).
% 9.02/3.71  tff(c_25603, plain, (![A_466, B_467]: (k4_xboole_0(A_466, k3_xboole_0(A_466, B_467))=k4_xboole_0(A_466, B_467))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.02/3.71  tff(c_25615, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_25579, c_25603])).
% 9.02/3.71  tff(c_25622, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_25615])).
% 9.02/3.71  tff(c_25717, plain, (![A_472, B_473, C_474]: (k4_xboole_0(k4_xboole_0(A_472, B_473), C_474)=k4_xboole_0(A_472, k2_xboole_0(B_473, C_474)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_25720, plain, (![A_472, B_473, C_474, C_11]: (k4_xboole_0(k4_xboole_0(A_472, k2_xboole_0(B_473, C_474)), C_11)=k4_xboole_0(k4_xboole_0(A_472, B_473), k2_xboole_0(C_474, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_25717, c_14])).
% 9.02/3.71  tff(c_27798, plain, (![A_518, B_519, C_520, C_521]: (k4_xboole_0(A_518, k2_xboole_0(k2_xboole_0(B_519, C_520), C_521))=k4_xboole_0(A_518, k2_xboole_0(B_519, k2_xboole_0(C_520, C_521))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_25720])).
% 9.02/3.71  tff(c_25751, plain, (![C_474]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_474))=k4_xboole_0('#skF_1', C_474))), inference(superposition, [status(thm), theory('equality')], [c_25622, c_25717])).
% 9.02/3.71  tff(c_28126, plain, (![C_524]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_524)))=k4_xboole_0('#skF_1', C_524))), inference(superposition, [status(thm), theory('equality')], [c_27798, c_25751])).
% 9.02/3.71  tff(c_28165, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_28126])).
% 9.02/3.71  tff(c_28175, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25622, c_28165])).
% 9.02/3.71  tff(c_28197, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28175, c_18])).
% 9.02/3.71  tff(c_28205, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25602, c_28197])).
% 9.02/3.71  tff(c_28207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25681, c_28205])).
% 9.02/3.71  tff(c_28208, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_25676])).
% 9.02/3.71  tff(c_28213, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_28208])).
% 9.02/3.71  tff(c_28209, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_25676])).
% 9.02/3.71  tff(c_28217, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28209, c_4])).
% 9.02/3.71  tff(c_28221, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28217, c_16])).
% 9.02/3.71  tff(c_28224, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28221])).
% 9.02/3.71  tff(c_28275, plain, (![A_527, B_528, C_529]: (k4_xboole_0(k4_xboole_0(A_527, B_528), C_529)=k4_xboole_0(A_527, k2_xboole_0(B_528, C_529)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.02/3.71  tff(c_28585, plain, (![C_536]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_536))=k4_xboole_0('#skF_1', C_536))), inference(superposition, [status(thm), theory('equality')], [c_28224, c_28275])).
% 9.02/3.71  tff(c_29640, plain, (![A_555]: (k4_xboole_0('#skF_1', k2_xboole_0(A_555, '#skF_2'))=k4_xboole_0('#skF_1', A_555))), inference(superposition, [status(thm), theory('equality')], [c_2, c_28585])).
% 9.02/3.71  tff(c_29678, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_29640, c_25622])).
% 9.02/3.71  tff(c_29754, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29678, c_18])).
% 9.02/3.71  tff(c_29760, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25602, c_29754])).
% 9.02/3.71  tff(c_29762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28213, c_29760])).
% 9.02/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.02/3.71  
% 9.02/3.71  Inference rules
% 9.02/3.71  ----------------------
% 9.02/3.71  #Ref     : 0
% 9.02/3.71  #Sup     : 7138
% 9.02/3.71  #Fact    : 0
% 9.02/3.71  #Define  : 0
% 9.02/3.71  #Split   : 10
% 9.02/3.71  #Chain   : 0
% 9.02/3.71  #Close   : 0
% 9.02/3.71  
% 9.02/3.71  Ordering : KBO
% 9.02/3.71  
% 9.02/3.71  Simplification rules
% 9.02/3.71  ----------------------
% 9.02/3.71  #Subsume      : 18
% 9.02/3.71  #Demod        : 7418
% 9.02/3.71  #Tautology    : 4648
% 9.02/3.71  #SimpNegUnit  : 9
% 9.02/3.71  #BackRed      : 13
% 9.02/3.71  
% 9.02/3.71  #Partial instantiations: 0
% 9.02/3.71  #Strategies tried      : 1
% 9.02/3.71  
% 9.02/3.71  Timing (in seconds)
% 9.02/3.71  ----------------------
% 9.02/3.71  Preprocessing        : 0.26
% 9.02/3.71  Parsing              : 0.14
% 9.02/3.71  CNF conversion       : 0.02
% 9.02/3.71  Main loop            : 2.62
% 9.02/3.71  Inferencing          : 0.69
% 9.02/3.71  Reduction            : 1.38
% 9.02/3.71  Demodulation         : 1.20
% 9.02/3.71  BG Simplification    : 0.09
% 9.02/3.71  Subsumption          : 0.33
% 9.02/3.71  Abstraction          : 0.14
% 9.02/3.71  MUC search           : 0.00
% 9.02/3.71  Cooper               : 0.00
% 9.02/3.71  Total                : 2.95
% 9.02/3.71  Index Insertion      : 0.00
% 9.02/3.71  Index Deletion       : 0.00
% 9.02/3.71  Index Matching       : 0.00
% 9.02/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
