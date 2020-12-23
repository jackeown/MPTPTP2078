%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :  256 (1013 expanded)
%              Number of leaves         :   23 ( 347 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 (1391 expanded)
%              Number of equality atoms :  201 ( 840 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_110,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_118,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9059,plain,(
    ! [A_179,B_180,C_181] : k4_xboole_0(k4_xboole_0(A_179,B_180),C_181) = k4_xboole_0(A_179,k2_xboole_0(B_180,C_181)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9127,plain,(
    ! [A_179,B_180] : k4_xboole_0(A_179,k2_xboole_0(B_180,k1_xboole_0)) = k4_xboole_0(A_179,B_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_9059])).

tff(c_5077,plain,(
    ! [A_112,B_113,C_114] : k4_xboole_0(k4_xboole_0(A_112,B_113),C_114) = k4_xboole_0(A_112,k2_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5102,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k2_xboole_0(B_113,k1_xboole_0)) = k4_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_5077,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_165,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_4])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_102,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_108,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_131,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_131])).

tff(c_146,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_140])).

tff(c_301,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k4_xboole_0(A_34,B_35),C_36) = k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2907,plain,(
    ! [A_86,B_87,C_88] : k4_xboole_0(k4_xboole_0(A_86,B_87),k4_xboole_0(A_86,k2_xboole_0(B_87,C_88))) = k3_xboole_0(k4_xboole_0(A_86,B_87),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_18])).

tff(c_3082,plain,(
    ! [C_88] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_88))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2907])).

tff(c_3146,plain,(
    ! [C_88] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_88)) = k3_xboole_0('#skF_4',C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_146,c_3082])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_282,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_300,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_282])).

tff(c_5047,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_300])).

tff(c_5050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_5047])).

tff(c_5051,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_5075,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5051,c_4])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5177,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5075,c_16])).

tff(c_5180,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5177])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | k3_xboole_0(A_27,B_26) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_7081,plain,(
    ! [B_151,A_152] :
      ( k3_xboole_0(B_151,A_152) = k1_xboole_0
      | k3_xboole_0(A_152,B_151) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_7150,plain,(
    ! [A_153] : k3_xboole_0(k1_xboole_0,A_153) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7081])).

tff(c_197,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_18])).

tff(c_222,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_200])).

tff(c_7184,plain,(
    ! [B_31] : k4_xboole_0(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7150,c_222])).

tff(c_5947,plain,(
    ! [A_131,B_132,C_133] : k4_xboole_0(A_131,k2_xboole_0(k4_xboole_0(A_131,B_132),C_133)) = k4_xboole_0(k3_xboole_0(A_131,B_132),C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5077])).

tff(c_6063,plain,(
    ! [A_8,C_133] : k4_xboole_0(k3_xboole_0(A_8,k1_xboole_0),C_133) = k4_xboole_0(A_8,k2_xboole_0(A_8,C_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5947])).

tff(c_6092,plain,(
    ! [A_8,C_133] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_133)) = k4_xboole_0(k1_xboole_0,C_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6063])).

tff(c_7317,plain,(
    ! [A_8,C_133] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_133)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7184,c_6092])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5094,plain,(
    ! [A_112,B_113,B_15] : k4_xboole_0(A_112,k2_xboole_0(B_113,k4_xboole_0(k4_xboole_0(A_112,B_113),B_15))) = k3_xboole_0(k4_xboole_0(A_112,B_113),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_5077,c_18])).

tff(c_8617,plain,(
    ! [A_172,B_173,B_174] : k4_xboole_0(A_172,k2_xboole_0(B_173,k4_xboole_0(A_172,k2_xboole_0(B_173,B_174)))) = k3_xboole_0(k4_xboole_0(A_172,B_173),B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5094])).

tff(c_8824,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5180,c_8617])).

tff(c_8896,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7317,c_2,c_8824])).

tff(c_5098,plain,(
    ! [A_112,B_113,B_13] : k4_xboole_0(A_112,k2_xboole_0(B_113,k3_xboole_0(k4_xboole_0(A_112,B_113),B_13))) = k4_xboole_0(k4_xboole_0(A_112,B_113),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_5077,c_16])).

tff(c_5152,plain,(
    ! [A_112,B_113,B_13] : k4_xboole_0(A_112,k2_xboole_0(B_113,k3_xboole_0(k4_xboole_0(A_112,B_113),B_13))) = k4_xboole_0(A_112,k2_xboole_0(B_113,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5098])).

tff(c_8906,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8896,c_5152])).

tff(c_8921,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5102,c_5180,c_8906])).

tff(c_8927,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8921,c_8896])).

tff(c_8929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8927])).

tff(c_8930,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_8954,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8930,c_4])).

tff(c_9046,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8954,c_16])).

tff(c_9049,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9046])).

tff(c_10886,plain,(
    ! [B_217,A_218] :
      ( k3_xboole_0(B_217,A_218) = k1_xboole_0
      | k3_xboole_0(A_218,B_217) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_10938,plain,(
    ! [A_219] : k3_xboole_0(k1_xboole_0,A_219) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_10886])).

tff(c_8964,plain,(
    ! [A_175,B_176] : k4_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = k3_xboole_0(A_175,B_176) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8967,plain,(
    ! [A_175,B_176] : k4_xboole_0(A_175,k3_xboole_0(A_175,B_176)) = k3_xboole_0(A_175,k4_xboole_0(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8964,c_18])).

tff(c_8989,plain,(
    ! [A_175,B_176] : k3_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = k4_xboole_0(A_175,B_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8967])).

tff(c_10965,plain,(
    ! [B_176] : k4_xboole_0(k1_xboole_0,B_176) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10938,c_8989])).

tff(c_8988,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8964])).

tff(c_8996,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8988])).

tff(c_9096,plain,(
    ! [A_8,C_181] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_181)) = k4_xboole_0(k1_xboole_0,C_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_8996,c_9059])).

tff(c_9076,plain,(
    ! [A_179,B_180,B_15] : k4_xboole_0(A_179,k2_xboole_0(B_180,k4_xboole_0(k4_xboole_0(A_179,B_180),B_15))) = k3_xboole_0(k4_xboole_0(A_179,B_180),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_9059,c_18])).

tff(c_10538,plain,(
    ! [A_211,B_212,B_213] : k4_xboole_0(A_211,k2_xboole_0(B_212,k4_xboole_0(A_211,k2_xboole_0(B_212,B_213)))) = k3_xboole_0(k4_xboole_0(A_211,B_212),B_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9076])).

tff(c_10689,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9049,c_10538])).

tff(c_10738,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k4_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9096,c_2,c_10689])).

tff(c_11565,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_10738])).

tff(c_9080,plain,(
    ! [A_179,B_180,B_13] : k4_xboole_0(A_179,k2_xboole_0(B_180,k3_xboole_0(k4_xboole_0(A_179,B_180),B_13))) = k4_xboole_0(k4_xboole_0(A_179,B_180),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_9059,c_16])).

tff(c_9131,plain,(
    ! [A_179,B_180,B_13] : k4_xboole_0(A_179,k2_xboole_0(B_180,k3_xboole_0(k4_xboole_0(A_179,B_180),B_13))) = k4_xboole_0(A_179,k2_xboole_0(B_180,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9080])).

tff(c_11569,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11565,c_9131])).

tff(c_11583,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9127,c_9049,c_11569])).

tff(c_11589,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11583,c_11565])).

tff(c_11591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_11589])).

tff(c_11592,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_11621,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11592])).

tff(c_11629,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_11621])).

tff(c_19800,plain,(
    ! [A_359,B_360] : k4_xboole_0(A_359,k4_xboole_0(A_359,B_360)) = k3_xboole_0(A_359,B_360) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19833,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19800])).

tff(c_19844,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_19833])).

tff(c_19866,plain,(
    ! [A_362,B_363,C_364] : k4_xboole_0(k4_xboole_0(A_362,B_363),C_364) = k4_xboole_0(A_362,k2_xboole_0(B_363,C_364)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19940,plain,(
    ! [A_362,B_363] : k4_xboole_0(A_362,k2_xboole_0(B_363,k1_xboole_0)) = k4_xboole_0(A_362,B_363) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19866])).

tff(c_16953,plain,(
    ! [A_310,B_311] : k4_xboole_0(A_310,k4_xboole_0(A_310,B_311)) = k3_xboole_0(A_310,B_311) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16995,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_16953])).

tff(c_17009,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16995])).

tff(c_17061,plain,(
    ! [A_314,B_315,C_316] : k4_xboole_0(k4_xboole_0(A_314,B_315),C_316) = k4_xboole_0(A_314,k2_xboole_0(B_315,C_316)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17086,plain,(
    ! [A_314,B_315] : k4_xboole_0(A_314,k2_xboole_0(B_315,k1_xboole_0)) = k4_xboole_0(A_314,B_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_17061,c_12])).

tff(c_11677,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_11683,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11677,c_4])).

tff(c_11835,plain,(
    ! [A_232,B_233,C_234] : k4_xboole_0(k4_xboole_0(A_232,B_233),C_234) = k4_xboole_0(A_232,k2_xboole_0(B_233,C_234)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11908,plain,(
    ! [A_8,C_234] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,C_234)) = k4_xboole_0(A_8,C_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11835])).

tff(c_11901,plain,(
    ! [A_12,B_13,C_234] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_234)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11835])).

tff(c_12892,plain,(
    ! [A_255,B_256,C_257] : k4_xboole_0(A_255,k2_xboole_0(k3_xboole_0(A_255,B_256),C_257)) = k4_xboole_0(A_255,k2_xboole_0(B_256,C_257)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11901])).

tff(c_12967,plain,(
    ! [C_257] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_257)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_12892])).

tff(c_13075,plain,(
    ! [C_259] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_259)) = k4_xboole_0('#skF_4',C_259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11908,c_12967])).

tff(c_13101,plain,(
    ! [C_259] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_259)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_259)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13075,c_18])).

tff(c_13127,plain,(
    ! [C_259] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_259)) = k3_xboole_0('#skF_4',C_259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_13101])).

tff(c_11701,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_11733,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_11701])).

tff(c_16847,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13127,c_11733])).

tff(c_16850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11683,c_16847])).

tff(c_16851,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_16888,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16851,c_4])).

tff(c_16916,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16888,c_16])).

tff(c_16919,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16916])).

tff(c_17620,plain,(
    ! [B_329,A_330] :
      ( k3_xboole_0(B_329,A_330) = k1_xboole_0
      | k3_xboole_0(A_330,B_329) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_17671,plain,(
    ! [A_331] : k3_xboole_0(k1_xboole_0,A_331) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17620])).

tff(c_16962,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16953])).

tff(c_16998,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16962])).

tff(c_17679,plain,(
    ! [B_15] : k4_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17671,c_16998])).

tff(c_18405,plain,(
    ! [A_343,B_344,C_345] : k4_xboole_0(A_343,k2_xboole_0(k4_xboole_0(A_343,B_344),C_345)) = k4_xboole_0(k3_xboole_0(A_343,B_344),C_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_17061])).

tff(c_18553,plain,(
    ! [A_8,C_345] : k4_xboole_0(k3_xboole_0(A_8,k1_xboole_0),C_345) = k4_xboole_0(A_8,k2_xboole_0(A_8,C_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_18405])).

tff(c_18592,plain,(
    ! [A_8,C_345] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_345)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17679,c_10,c_18553])).

tff(c_17106,plain,(
    ! [A_314,B_315,B_15] : k4_xboole_0(A_314,k2_xboole_0(B_315,k4_xboole_0(k4_xboole_0(A_314,B_315),B_15))) = k3_xboole_0(k4_xboole_0(A_314,B_315),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_17061])).

tff(c_18913,plain,(
    ! [A_351,B_352,B_353] : k4_xboole_0(A_351,k2_xboole_0(B_352,k4_xboole_0(A_351,k2_xboole_0(B_352,B_353)))) = k3_xboole_0(k4_xboole_0(A_351,B_352),B_353) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_17106])).

tff(c_19088,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16919,c_18913])).

tff(c_19139,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18592,c_2,c_19088])).

tff(c_17082,plain,(
    ! [A_314,B_315,B_13] : k4_xboole_0(A_314,k2_xboole_0(B_315,k3_xboole_0(k4_xboole_0(A_314,B_315),B_13))) = k4_xboole_0(k4_xboole_0(A_314,B_315),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_17061,c_16])).

tff(c_17148,plain,(
    ! [A_314,B_315,B_13] : k4_xboole_0(A_314,k2_xboole_0(B_315,k3_xboole_0(k4_xboole_0(A_314,B_315),B_13))) = k4_xboole_0(A_314,k2_xboole_0(B_315,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_17082])).

tff(c_19609,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19139,c_17148])).

tff(c_19623,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17086,c_16919,c_19609])).

tff(c_19733,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19623,c_18])).

tff(c_19739,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17009,c_19733])).

tff(c_19741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11629,c_19739])).

tff(c_19742,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_19761,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19742,c_4])).

tff(c_19783,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_19761,c_16])).

tff(c_19786,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19783])).

tff(c_21805,plain,(
    ! [B_402,A_403] :
      ( k3_xboole_0(B_402,A_403) = k1_xboole_0
      | k3_xboole_0(A_403,B_402) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_21867,plain,(
    ! [A_7] : k3_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_21805])).

tff(c_20728,plain,(
    ! [A_383,B_384,C_385] : k4_xboole_0(A_383,k2_xboole_0(k4_xboole_0(A_383,B_384),C_385)) = k4_xboole_0(k3_xboole_0(A_383,B_384),C_385) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_19866])).

tff(c_20844,plain,(
    ! [A_8,C_385] : k4_xboole_0(k3_xboole_0(A_8,k1_xboole_0),C_385) = k4_xboole_0(A_8,k2_xboole_0(A_8,C_385)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20728])).

tff(c_20873,plain,(
    ! [A_8,C_385] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_385)) = k4_xboole_0(k1_xboole_0,C_385) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20844])).

tff(c_19887,plain,(
    ! [A_362,B_363,B_13] : k4_xboole_0(A_362,k2_xboole_0(B_363,k3_xboole_0(k4_xboole_0(A_362,B_363),B_13))) = k4_xboole_0(k4_xboole_0(A_362,B_363),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_19866,c_16])).

tff(c_21970,plain,(
    ! [A_405,B_406,B_407] : k4_xboole_0(A_405,k2_xboole_0(B_406,k3_xboole_0(k4_xboole_0(A_405,B_406),B_407))) = k4_xboole_0(A_405,k2_xboole_0(B_406,B_407)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19887])).

tff(c_22169,plain,(
    ! [A_8,B_407] : k4_xboole_0(A_8,k2_xboole_0(A_8,k3_xboole_0(k1_xboole_0,B_407))) = k4_xboole_0(A_8,k2_xboole_0(A_8,B_407)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19844,c_21970])).

tff(c_22255,plain,(
    ! [B_407] : k4_xboole_0(k1_xboole_0,B_407) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19844,c_19940,c_21867,c_20873,c_22169])).

tff(c_22266,plain,(
    ! [A_8,C_385] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_385)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22255,c_20873])).

tff(c_19911,plain,(
    ! [A_362,B_363,B_15] : k4_xboole_0(A_362,k2_xboole_0(B_363,k4_xboole_0(k4_xboole_0(A_362,B_363),B_15))) = k3_xboole_0(k4_xboole_0(A_362,B_363),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_19866])).

tff(c_22620,plain,(
    ! [A_412,B_413,B_414] : k4_xboole_0(A_412,k2_xboole_0(B_413,k4_xboole_0(A_412,k2_xboole_0(B_413,B_414)))) = k3_xboole_0(k4_xboole_0(A_412,B_413),B_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19911])).

tff(c_22809,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19786,c_22620])).

tff(c_22865,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22266,c_2,c_22809])).

tff(c_19944,plain,(
    ! [A_362,B_363,B_13] : k4_xboole_0(A_362,k2_xboole_0(B_363,k3_xboole_0(k4_xboole_0(A_362,B_363),B_13))) = k4_xboole_0(A_362,k2_xboole_0(B_363,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19887])).

tff(c_22869,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22865,c_19944])).

tff(c_22883,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19940,c_19786,c_22869])).

tff(c_22909,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22883,c_18])).

tff(c_22915,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19844,c_22909])).

tff(c_22917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11629,c_22915])).

tff(c_22918,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_11592])).

tff(c_22925,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22918,c_4])).

tff(c_23301,plain,(
    ! [A_425,B_426,C_427] : k4_xboole_0(k4_xboole_0(A_425,B_426),C_427) = k4_xboole_0(A_425,k2_xboole_0(B_426,C_427)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23383,plain,(
    ! [A_8,C_427] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,C_427)) = k4_xboole_0(A_8,C_427) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_23301])).

tff(c_23361,plain,(
    ! [A_425,B_426,B_15] : k4_xboole_0(A_425,k2_xboole_0(B_426,k4_xboole_0(k4_xboole_0(A_425,B_426),B_15))) = k3_xboole_0(k4_xboole_0(A_425,B_426),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_23301])).

tff(c_25820,plain,(
    ! [A_468,B_469,B_470] : k4_xboole_0(A_468,k2_xboole_0(B_469,k4_xboole_0(A_468,k2_xboole_0(B_469,B_470)))) = k3_xboole_0(k4_xboole_0(A_468,B_469),B_470) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_23361])).

tff(c_25974,plain,(
    ! [A_8,C_427] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_8,C_427))) = k3_xboole_0(k4_xboole_0(A_8,k1_xboole_0),C_427) ),
    inference(superposition,[status(thm),theory(equality)],[c_23383,c_25820])).

tff(c_26057,plain,(
    ! [A_8,C_427] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_8,C_427))) = k3_xboole_0(A_8,C_427) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25974])).

tff(c_23376,plain,(
    ! [A_12,B_13,C_427] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_427)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_427) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_23301])).

tff(c_24620,plain,(
    ! [A_450,B_451,C_452] : k4_xboole_0(A_450,k2_xboole_0(k3_xboole_0(A_450,B_451),C_452)) = k4_xboole_0(A_450,k2_xboole_0(B_451,C_452)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_23376])).

tff(c_24712,plain,(
    ! [C_452] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_452)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_452)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_24620])).

tff(c_24750,plain,(
    ! [C_452] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_452)) = k4_xboole_0('#skF_4',C_452) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23383,c_24712])).

tff(c_28821,plain,(
    ! [A_505,C_506] : k4_xboole_0(A_505,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_505,C_506))) = k3_xboole_0(A_505,C_506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25974])).

tff(c_28965,plain,(
    ! [C_452] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4',C_452))) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_452)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24750,c_28821])).

tff(c_29105,plain,(
    ! [C_452] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_452)) = k3_xboole_0('#skF_4',C_452) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26057,c_28965])).

tff(c_23127,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_23161,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_23127])).

tff(c_30007,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29105,c_23161])).

tff(c_30010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22925,c_30007])).

tff(c_30012,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_11593,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22919,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_11592])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_30056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30012,c_11593,c_22919,c_32])).

tff(c_30058,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30145,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30153,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_30145])).

tff(c_30355,plain,(
    ! [A_527,B_528,C_529] : k4_xboole_0(k4_xboole_0(A_527,B_528),C_529) = k4_xboole_0(A_527,k2_xboole_0(B_528,C_529)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30423,plain,(
    ! [A_527,B_528] : k4_xboole_0(A_527,k2_xboole_0(B_528,k1_xboole_0)) = k4_xboole_0(A_527,B_528) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_30355])).

tff(c_30057,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30072,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30057,c_4])).

tff(c_30159,plain,(
    ! [A_519,B_520] : k4_xboole_0(A_519,k3_xboole_0(A_519,B_520)) = k4_xboole_0(A_519,B_520) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30174,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30072,c_30159])).

tff(c_30185,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30174])).

tff(c_30233,plain,(
    ! [B_523,A_524] :
      ( k3_xboole_0(B_523,A_524) = k1_xboole_0
      | k3_xboole_0(A_524,B_523) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_30251,plain,(
    ! [A_525] : k3_xboole_0(k1_xboole_0,A_525) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_30233])).

tff(c_30265,plain,(
    ! [A_525] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_525) ),
    inference(superposition,[status(thm),theory(equality)],[c_30251,c_16])).

tff(c_30291,plain,(
    ! [A_525] : k4_xboole_0(k1_xboole_0,A_525) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30265])).

tff(c_30082,plain,(
    ! [A_515,B_516] : k4_xboole_0(A_515,k4_xboole_0(A_515,B_516)) = k3_xboole_0(A_515,B_516) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30097,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_30082])).

tff(c_30100,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30097])).

tff(c_30405,plain,(
    ! [A_8,C_529] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_529)) = k4_xboole_0(k1_xboole_0,C_529) ),
    inference(superposition,[status(thm),theory(equality)],[c_30100,c_30355])).

tff(c_30433,plain,(
    ! [A_8,C_529] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_529)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30291,c_30405])).

tff(c_30376,plain,(
    ! [A_527,B_528,B_15] : k4_xboole_0(A_527,k2_xboole_0(B_528,k4_xboole_0(k4_xboole_0(A_527,B_528),B_15))) = k3_xboole_0(k4_xboole_0(A_527,B_528),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_30355,c_18])).

tff(c_34744,plain,(
    ! [A_608,B_609,B_610] : k4_xboole_0(A_608,k2_xboole_0(B_609,k4_xboole_0(A_608,k2_xboole_0(B_609,B_610)))) = k3_xboole_0(k4_xboole_0(A_608,B_609),B_610) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30376])).

tff(c_34993,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_1')) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30185,c_34744])).

tff(c_35068,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30433,c_2,c_34993])).

tff(c_30402,plain,(
    ! [A_527,B_528,B_13] : k4_xboole_0(A_527,k2_xboole_0(B_528,k3_xboole_0(k4_xboole_0(A_527,B_528),B_13))) = k4_xboole_0(k4_xboole_0(A_527,B_528),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_30355])).

tff(c_30432,plain,(
    ! [A_527,B_528,B_13] : k4_xboole_0(A_527,k2_xboole_0(B_528,k3_xboole_0(k4_xboole_0(A_527,B_528),B_13))) = k4_xboole_0(A_527,k2_xboole_0(B_528,B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30402])).

tff(c_35073,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35068,c_30432])).

tff(c_35090,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30423,c_30185,c_35073])).

tff(c_35097,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35090,c_35068])).

tff(c_35099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30153,c_35097])).

tff(c_35101,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35110,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35101,c_22])).

tff(c_35111,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30058,c_35110])).

tff(c_35119,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_35111])).

tff(c_35107,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35101,c_4])).

tff(c_35141,plain,(
    ! [A_611,B_612] : k4_xboole_0(A_611,k3_xboole_0(A_611,B_612)) = k4_xboole_0(A_611,B_612) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35159,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35107,c_35141])).

tff(c_35174,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35159])).

tff(c_35273,plain,(
    ! [A_617,B_618,C_619] : k4_xboole_0(k4_xboole_0(A_617,B_618),C_619) = k4_xboole_0(A_617,k2_xboole_0(B_618,C_619)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35769,plain,(
    ! [C_630] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_630)) = k4_xboole_0('#skF_1',C_630) ),
    inference(superposition,[status(thm),theory(equality)],[c_35174,c_35273])).

tff(c_36466,plain,(
    ! [B_648] : k4_xboole_0('#skF_1',k2_xboole_0(B_648,'#skF_2')) = k4_xboole_0('#skF_1',B_648) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_35769])).

tff(c_35162,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30072,c_35141])).

tff(c_35175,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35162])).

tff(c_36493,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_36466,c_35175])).

tff(c_36548,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36493,c_18])).

tff(c_36553,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30100,c_36548])).

tff(c_36555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35119,c_36553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.71/4.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.65  
% 11.91/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.66  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.91/4.66  
% 11.91/4.66  %Foreground sorts:
% 11.91/4.66  
% 11.91/4.66  
% 11.91/4.66  %Background operators:
% 11.91/4.66  
% 11.91/4.66  
% 11.91/4.66  %Foreground operators:
% 11.91/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.91/4.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.91/4.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.91/4.66  tff('#skF_5', type, '#skF_5': $i).
% 11.91/4.66  tff('#skF_6', type, '#skF_6': $i).
% 11.91/4.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.91/4.66  tff('#skF_2', type, '#skF_2': $i).
% 11.91/4.66  tff('#skF_3', type, '#skF_3': $i).
% 11.91/4.66  tff('#skF_1', type, '#skF_1': $i).
% 11.91/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.91/4.66  tff('#skF_4', type, '#skF_4': $i).
% 11.91/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.91/4.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.91/4.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.91/4.66  
% 11.91/4.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.91/4.72  tff(f_62, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.91/4.72  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.91/4.72  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.91/4.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.91/4.72  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.91/4.72  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.91/4.72  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 11.91/4.72  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.91/4.72  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.91/4.72  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_110, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 11.91/4.72  tff(c_118, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_110])).
% 11.91/4.72  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.91/4.72  tff(c_9059, plain, (![A_179, B_180, C_181]: (k4_xboole_0(k4_xboole_0(A_179, B_180), C_181)=k4_xboole_0(A_179, k2_xboole_0(B_180, C_181)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_9127, plain, (![A_179, B_180]: (k4_xboole_0(A_179, k2_xboole_0(B_180, k1_xboole_0))=k4_xboole_0(A_179, B_180))), inference(superposition, [status(thm), theory('equality')], [c_12, c_9059])).
% 11.91/4.72  tff(c_5077, plain, (![A_112, B_113, C_114]: (k4_xboole_0(k4_xboole_0(A_112, B_113), C_114)=k4_xboole_0(A_112, k2_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_5102, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k2_xboole_0(B_113, k1_xboole_0))=k4_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_5077, c_12])).
% 11.91/4.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.91/4.72  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_31, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 11.91/4.72  tff(c_165, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 11.91/4.72  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.91/4.72  tff(c_171, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_4])).
% 11.91/4.72  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 11.91/4.72  tff(c_102, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 11.91/4.72  tff(c_108, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_102, c_4])).
% 11.91/4.72  tff(c_131, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.91/4.72  tff(c_140, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_108, c_131])).
% 11.91/4.72  tff(c_146, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_140])).
% 11.91/4.72  tff(c_301, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k4_xboole_0(A_34, B_35), C_36)=k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_2907, plain, (![A_86, B_87, C_88]: (k4_xboole_0(k4_xboole_0(A_86, B_87), k4_xboole_0(A_86, k2_xboole_0(B_87, C_88)))=k3_xboole_0(k4_xboole_0(A_86, B_87), C_88))), inference(superposition, [status(thm), theory('equality')], [c_301, c_18])).
% 11.91/4.72  tff(c_3082, plain, (![C_88]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_88)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_88))), inference(superposition, [status(thm), theory('equality')], [c_146, c_2907])).
% 11.91/4.72  tff(c_3146, plain, (![C_88]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_88))=k3_xboole_0('#skF_4', C_88))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_146, c_3082])).
% 11.91/4.72  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_33, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 11.91/4.72  tff(c_282, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_300, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_282])).
% 11.91/4.72  tff(c_5047, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_300])).
% 11.91/4.72  tff(c_5050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_5047])).
% 11.91/4.72  tff(c_5051, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_5075, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5051, c_4])).
% 11.91/4.72  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.91/4.72  tff(c_5177, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5075, c_16])).
% 11.91/4.72  tff(c_5180, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5177])).
% 11.91/4.72  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.91/4.72  tff(c_85, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.91/4.72  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.91/4.72  tff(c_94, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | k3_xboole_0(A_27, B_26)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_8])).
% 11.91/4.72  tff(c_7081, plain, (![B_151, A_152]: (k3_xboole_0(B_151, A_152)=k1_xboole_0 | k3_xboole_0(A_152, B_151)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_4])).
% 11.91/4.72  tff(c_7150, plain, (![A_153]: (k3_xboole_0(k1_xboole_0, A_153)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_7081])).
% 11.91/4.72  tff(c_197, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_200, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k3_xboole_0(A_30, k4_xboole_0(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_18])).
% 11.91/4.72  tff(c_222, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_200])).
% 11.91/4.72  tff(c_7184, plain, (![B_31]: (k4_xboole_0(k1_xboole_0, B_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7150, c_222])).
% 11.91/4.72  tff(c_5947, plain, (![A_131, B_132, C_133]: (k4_xboole_0(A_131, k2_xboole_0(k4_xboole_0(A_131, B_132), C_133))=k4_xboole_0(k3_xboole_0(A_131, B_132), C_133))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5077])).
% 11.91/4.72  tff(c_6063, plain, (![A_8, C_133]: (k4_xboole_0(k3_xboole_0(A_8, k1_xboole_0), C_133)=k4_xboole_0(A_8, k2_xboole_0(A_8, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5947])).
% 11.91/4.72  tff(c_6092, plain, (![A_8, C_133]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_133))=k4_xboole_0(k1_xboole_0, C_133))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6063])).
% 11.91/4.72  tff(c_7317, plain, (![A_8, C_133]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_133))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7184, c_6092])).
% 11.91/4.72  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_5094, plain, (![A_112, B_113, B_15]: (k4_xboole_0(A_112, k2_xboole_0(B_113, k4_xboole_0(k4_xboole_0(A_112, B_113), B_15)))=k3_xboole_0(k4_xboole_0(A_112, B_113), B_15))), inference(superposition, [status(thm), theory('equality')], [c_5077, c_18])).
% 11.91/4.72  tff(c_8617, plain, (![A_172, B_173, B_174]: (k4_xboole_0(A_172, k2_xboole_0(B_173, k4_xboole_0(A_172, k2_xboole_0(B_173, B_174))))=k3_xboole_0(k4_xboole_0(A_172, B_173), B_174))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5094])).
% 11.91/4.72  tff(c_8824, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5180, c_8617])).
% 11.91/4.72  tff(c_8896, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7317, c_2, c_8824])).
% 11.91/4.72  tff(c_5098, plain, (![A_112, B_113, B_13]: (k4_xboole_0(A_112, k2_xboole_0(B_113, k3_xboole_0(k4_xboole_0(A_112, B_113), B_13)))=k4_xboole_0(k4_xboole_0(A_112, B_113), B_13))), inference(superposition, [status(thm), theory('equality')], [c_5077, c_16])).
% 11.91/4.72  tff(c_5152, plain, (![A_112, B_113, B_13]: (k4_xboole_0(A_112, k2_xboole_0(B_113, k3_xboole_0(k4_xboole_0(A_112, B_113), B_13)))=k4_xboole_0(A_112, k2_xboole_0(B_113, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5098])).
% 11.91/4.72  tff(c_8906, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8896, c_5152])).
% 11.91/4.72  tff(c_8921, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5102, c_5180, c_8906])).
% 11.91/4.72  tff(c_8927, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8921, c_8896])).
% 11.91/4.72  tff(c_8929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_8927])).
% 11.91/4.72  tff(c_8930, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 11.91/4.72  tff(c_8954, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8930, c_4])).
% 11.91/4.72  tff(c_9046, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8954, c_16])).
% 11.91/4.72  tff(c_9049, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9046])).
% 11.91/4.72  tff(c_10886, plain, (![B_217, A_218]: (k3_xboole_0(B_217, A_218)=k1_xboole_0 | k3_xboole_0(A_218, B_217)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_4])).
% 11.91/4.72  tff(c_10938, plain, (![A_219]: (k3_xboole_0(k1_xboole_0, A_219)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_10886])).
% 11.91/4.72  tff(c_8964, plain, (![A_175, B_176]: (k4_xboole_0(A_175, k4_xboole_0(A_175, B_176))=k3_xboole_0(A_175, B_176))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_8967, plain, (![A_175, B_176]: (k4_xboole_0(A_175, k3_xboole_0(A_175, B_176))=k3_xboole_0(A_175, k4_xboole_0(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_8964, c_18])).
% 11.91/4.72  tff(c_8989, plain, (![A_175, B_176]: (k3_xboole_0(A_175, k4_xboole_0(A_175, B_176))=k4_xboole_0(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8967])).
% 11.91/4.72  tff(c_10965, plain, (![B_176]: (k4_xboole_0(k1_xboole_0, B_176)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10938, c_8989])).
% 11.91/4.72  tff(c_8988, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8964])).
% 11.91/4.72  tff(c_8996, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8988])).
% 11.91/4.72  tff(c_9096, plain, (![A_8, C_181]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_181))=k4_xboole_0(k1_xboole_0, C_181))), inference(superposition, [status(thm), theory('equality')], [c_8996, c_9059])).
% 11.91/4.72  tff(c_9076, plain, (![A_179, B_180, B_15]: (k4_xboole_0(A_179, k2_xboole_0(B_180, k4_xboole_0(k4_xboole_0(A_179, B_180), B_15)))=k3_xboole_0(k4_xboole_0(A_179, B_180), B_15))), inference(superposition, [status(thm), theory('equality')], [c_9059, c_18])).
% 11.91/4.72  tff(c_10538, plain, (![A_211, B_212, B_213]: (k4_xboole_0(A_211, k2_xboole_0(B_212, k4_xboole_0(A_211, k2_xboole_0(B_212, B_213))))=k3_xboole_0(k4_xboole_0(A_211, B_212), B_213))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9076])).
% 11.91/4.72  tff(c_10689, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9049, c_10538])).
% 11.91/4.72  tff(c_10738, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k4_xboole_0(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9096, c_2, c_10689])).
% 11.91/4.72  tff(c_11565, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_10738])).
% 11.91/4.72  tff(c_9080, plain, (![A_179, B_180, B_13]: (k4_xboole_0(A_179, k2_xboole_0(B_180, k3_xboole_0(k4_xboole_0(A_179, B_180), B_13)))=k4_xboole_0(k4_xboole_0(A_179, B_180), B_13))), inference(superposition, [status(thm), theory('equality')], [c_9059, c_16])).
% 11.91/4.72  tff(c_9131, plain, (![A_179, B_180, B_13]: (k4_xboole_0(A_179, k2_xboole_0(B_180, k3_xboole_0(k4_xboole_0(A_179, B_180), B_13)))=k4_xboole_0(A_179, k2_xboole_0(B_180, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9080])).
% 11.91/4.72  tff(c_11569, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11565, c_9131])).
% 11.91/4.72  tff(c_11583, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9127, c_9049, c_11569])).
% 11.91/4.72  tff(c_11589, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11583, c_11565])).
% 11.91/4.72  tff(c_11591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_11589])).
% 11.91/4.72  tff(c_11592, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 11.91/4.72  tff(c_11621, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_11592])).
% 11.91/4.72  tff(c_11629, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_11621])).
% 11.91/4.72  tff(c_19800, plain, (![A_359, B_360]: (k4_xboole_0(A_359, k4_xboole_0(A_359, B_360))=k3_xboole_0(A_359, B_360))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_19833, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_19800])).
% 11.91/4.72  tff(c_19844, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_19833])).
% 11.91/4.72  tff(c_19866, plain, (![A_362, B_363, C_364]: (k4_xboole_0(k4_xboole_0(A_362, B_363), C_364)=k4_xboole_0(A_362, k2_xboole_0(B_363, C_364)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_19940, plain, (![A_362, B_363]: (k4_xboole_0(A_362, k2_xboole_0(B_363, k1_xboole_0))=k4_xboole_0(A_362, B_363))), inference(superposition, [status(thm), theory('equality')], [c_12, c_19866])).
% 11.91/4.72  tff(c_16953, plain, (![A_310, B_311]: (k4_xboole_0(A_310, k4_xboole_0(A_310, B_311))=k3_xboole_0(A_310, B_311))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_16995, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_16953])).
% 11.91/4.72  tff(c_17009, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16995])).
% 11.91/4.72  tff(c_17061, plain, (![A_314, B_315, C_316]: (k4_xboole_0(k4_xboole_0(A_314, B_315), C_316)=k4_xboole_0(A_314, k2_xboole_0(B_315, C_316)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_17086, plain, (![A_314, B_315]: (k4_xboole_0(A_314, k2_xboole_0(B_315, k1_xboole_0))=k4_xboole_0(A_314, B_315))), inference(superposition, [status(thm), theory('equality')], [c_17061, c_12])).
% 11.91/4.72  tff(c_11677, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 11.91/4.72  tff(c_11683, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_11677, c_4])).
% 11.91/4.72  tff(c_11835, plain, (![A_232, B_233, C_234]: (k4_xboole_0(k4_xboole_0(A_232, B_233), C_234)=k4_xboole_0(A_232, k2_xboole_0(B_233, C_234)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_11908, plain, (![A_8, C_234]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, C_234))=k4_xboole_0(A_8, C_234))), inference(superposition, [status(thm), theory('equality')], [c_12, c_11835])).
% 11.91/4.72  tff(c_11901, plain, (![A_12, B_13, C_234]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_234))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_234))), inference(superposition, [status(thm), theory('equality')], [c_16, c_11835])).
% 11.91/4.72  tff(c_12892, plain, (![A_255, B_256, C_257]: (k4_xboole_0(A_255, k2_xboole_0(k3_xboole_0(A_255, B_256), C_257))=k4_xboole_0(A_255, k2_xboole_0(B_256, C_257)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_11901])).
% 11.91/4.72  tff(c_12967, plain, (![C_257]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_257))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_257)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_12892])).
% 11.91/4.72  tff(c_13075, plain, (![C_259]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_259))=k4_xboole_0('#skF_4', C_259))), inference(demodulation, [status(thm), theory('equality')], [c_11908, c_12967])).
% 11.91/4.72  tff(c_13101, plain, (![C_259]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_259))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_259)))), inference(superposition, [status(thm), theory('equality')], [c_13075, c_18])).
% 11.91/4.72  tff(c_13127, plain, (![C_259]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_259))=k3_xboole_0('#skF_4', C_259))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_13101])).
% 11.91/4.72  tff(c_11701, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_11733, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_11701])).
% 11.91/4.72  tff(c_16847, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13127, c_11733])).
% 11.91/4.72  tff(c_16850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11683, c_16847])).
% 11.91/4.72  tff(c_16851, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_16888, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16851, c_4])).
% 11.91/4.72  tff(c_16916, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16888, c_16])).
% 11.91/4.72  tff(c_16919, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16916])).
% 11.91/4.72  tff(c_17620, plain, (![B_329, A_330]: (k3_xboole_0(B_329, A_330)=k1_xboole_0 | k3_xboole_0(A_330, B_329)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_4])).
% 11.91/4.72  tff(c_17671, plain, (![A_331]: (k3_xboole_0(k1_xboole_0, A_331)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_17620])).
% 11.91/4.72  tff(c_16962, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16953])).
% 11.91/4.72  tff(c_16998, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16962])).
% 11.91/4.72  tff(c_17679, plain, (![B_15]: (k4_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17671, c_16998])).
% 11.91/4.72  tff(c_18405, plain, (![A_343, B_344, C_345]: (k4_xboole_0(A_343, k2_xboole_0(k4_xboole_0(A_343, B_344), C_345))=k4_xboole_0(k3_xboole_0(A_343, B_344), C_345))), inference(superposition, [status(thm), theory('equality')], [c_18, c_17061])).
% 11.91/4.72  tff(c_18553, plain, (![A_8, C_345]: (k4_xboole_0(k3_xboole_0(A_8, k1_xboole_0), C_345)=k4_xboole_0(A_8, k2_xboole_0(A_8, C_345)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_18405])).
% 11.91/4.72  tff(c_18592, plain, (![A_8, C_345]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_345))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17679, c_10, c_18553])).
% 11.91/4.72  tff(c_17106, plain, (![A_314, B_315, B_15]: (k4_xboole_0(A_314, k2_xboole_0(B_315, k4_xboole_0(k4_xboole_0(A_314, B_315), B_15)))=k3_xboole_0(k4_xboole_0(A_314, B_315), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_17061])).
% 11.91/4.72  tff(c_18913, plain, (![A_351, B_352, B_353]: (k4_xboole_0(A_351, k2_xboole_0(B_352, k4_xboole_0(A_351, k2_xboole_0(B_352, B_353))))=k3_xboole_0(k4_xboole_0(A_351, B_352), B_353))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_17106])).
% 11.91/4.72  tff(c_19088, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16919, c_18913])).
% 11.91/4.72  tff(c_19139, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18592, c_2, c_19088])).
% 11.91/4.72  tff(c_17082, plain, (![A_314, B_315, B_13]: (k4_xboole_0(A_314, k2_xboole_0(B_315, k3_xboole_0(k4_xboole_0(A_314, B_315), B_13)))=k4_xboole_0(k4_xboole_0(A_314, B_315), B_13))), inference(superposition, [status(thm), theory('equality')], [c_17061, c_16])).
% 11.91/4.72  tff(c_17148, plain, (![A_314, B_315, B_13]: (k4_xboole_0(A_314, k2_xboole_0(B_315, k3_xboole_0(k4_xboole_0(A_314, B_315), B_13)))=k4_xboole_0(A_314, k2_xboole_0(B_315, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_17082])).
% 11.91/4.72  tff(c_19609, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_19139, c_17148])).
% 11.91/4.72  tff(c_19623, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17086, c_16919, c_19609])).
% 11.91/4.72  tff(c_19733, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19623, c_18])).
% 11.91/4.72  tff(c_19739, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17009, c_19733])).
% 11.91/4.72  tff(c_19741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11629, c_19739])).
% 11.91/4.72  tff(c_19742, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 11.91/4.72  tff(c_19761, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_19742, c_4])).
% 11.91/4.72  tff(c_19783, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_19761, c_16])).
% 11.91/4.72  tff(c_19786, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19783])).
% 11.91/4.72  tff(c_21805, plain, (![B_402, A_403]: (k3_xboole_0(B_402, A_403)=k1_xboole_0 | k3_xboole_0(A_403, B_402)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_4])).
% 11.91/4.72  tff(c_21867, plain, (![A_7]: (k3_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_21805])).
% 11.91/4.72  tff(c_20728, plain, (![A_383, B_384, C_385]: (k4_xboole_0(A_383, k2_xboole_0(k4_xboole_0(A_383, B_384), C_385))=k4_xboole_0(k3_xboole_0(A_383, B_384), C_385))), inference(superposition, [status(thm), theory('equality')], [c_18, c_19866])).
% 11.91/4.72  tff(c_20844, plain, (![A_8, C_385]: (k4_xboole_0(k3_xboole_0(A_8, k1_xboole_0), C_385)=k4_xboole_0(A_8, k2_xboole_0(A_8, C_385)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20728])).
% 11.91/4.72  tff(c_20873, plain, (![A_8, C_385]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_385))=k4_xboole_0(k1_xboole_0, C_385))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20844])).
% 11.91/4.72  tff(c_19887, plain, (![A_362, B_363, B_13]: (k4_xboole_0(A_362, k2_xboole_0(B_363, k3_xboole_0(k4_xboole_0(A_362, B_363), B_13)))=k4_xboole_0(k4_xboole_0(A_362, B_363), B_13))), inference(superposition, [status(thm), theory('equality')], [c_19866, c_16])).
% 11.91/4.72  tff(c_21970, plain, (![A_405, B_406, B_407]: (k4_xboole_0(A_405, k2_xboole_0(B_406, k3_xboole_0(k4_xboole_0(A_405, B_406), B_407)))=k4_xboole_0(A_405, k2_xboole_0(B_406, B_407)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19887])).
% 11.91/4.72  tff(c_22169, plain, (![A_8, B_407]: (k4_xboole_0(A_8, k2_xboole_0(A_8, k3_xboole_0(k1_xboole_0, B_407)))=k4_xboole_0(A_8, k2_xboole_0(A_8, B_407)))), inference(superposition, [status(thm), theory('equality')], [c_19844, c_21970])).
% 11.91/4.72  tff(c_22255, plain, (![B_407]: (k4_xboole_0(k1_xboole_0, B_407)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19844, c_19940, c_21867, c_20873, c_22169])).
% 11.91/4.72  tff(c_22266, plain, (![A_8, C_385]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_385))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22255, c_20873])).
% 11.91/4.72  tff(c_19911, plain, (![A_362, B_363, B_15]: (k4_xboole_0(A_362, k2_xboole_0(B_363, k4_xboole_0(k4_xboole_0(A_362, B_363), B_15)))=k3_xboole_0(k4_xboole_0(A_362, B_363), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_19866])).
% 11.91/4.72  tff(c_22620, plain, (![A_412, B_413, B_414]: (k4_xboole_0(A_412, k2_xboole_0(B_413, k4_xboole_0(A_412, k2_xboole_0(B_413, B_414))))=k3_xboole_0(k4_xboole_0(A_412, B_413), B_414))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19911])).
% 11.91/4.72  tff(c_22809, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19786, c_22620])).
% 11.91/4.72  tff(c_22865, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22266, c_2, c_22809])).
% 11.91/4.72  tff(c_19944, plain, (![A_362, B_363, B_13]: (k4_xboole_0(A_362, k2_xboole_0(B_363, k3_xboole_0(k4_xboole_0(A_362, B_363), B_13)))=k4_xboole_0(A_362, k2_xboole_0(B_363, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19887])).
% 11.91/4.72  tff(c_22869, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22865, c_19944])).
% 11.91/4.72  tff(c_22883, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19940, c_19786, c_22869])).
% 11.91/4.72  tff(c_22909, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22883, c_18])).
% 11.91/4.72  tff(c_22915, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19844, c_22909])).
% 11.91/4.72  tff(c_22917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11629, c_22915])).
% 11.91/4.72  tff(c_22918, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_11592])).
% 11.91/4.72  tff(c_22925, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_22918, c_4])).
% 11.91/4.72  tff(c_23301, plain, (![A_425, B_426, C_427]: (k4_xboole_0(k4_xboole_0(A_425, B_426), C_427)=k4_xboole_0(A_425, k2_xboole_0(B_426, C_427)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_23383, plain, (![A_8, C_427]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, C_427))=k4_xboole_0(A_8, C_427))), inference(superposition, [status(thm), theory('equality')], [c_12, c_23301])).
% 11.91/4.72  tff(c_23361, plain, (![A_425, B_426, B_15]: (k4_xboole_0(A_425, k2_xboole_0(B_426, k4_xboole_0(k4_xboole_0(A_425, B_426), B_15)))=k3_xboole_0(k4_xboole_0(A_425, B_426), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_23301])).
% 11.91/4.72  tff(c_25820, plain, (![A_468, B_469, B_470]: (k4_xboole_0(A_468, k2_xboole_0(B_469, k4_xboole_0(A_468, k2_xboole_0(B_469, B_470))))=k3_xboole_0(k4_xboole_0(A_468, B_469), B_470))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_23361])).
% 11.91/4.72  tff(c_25974, plain, (![A_8, C_427]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_8, C_427)))=k3_xboole_0(k4_xboole_0(A_8, k1_xboole_0), C_427))), inference(superposition, [status(thm), theory('equality')], [c_23383, c_25820])).
% 11.91/4.72  tff(c_26057, plain, (![A_8, C_427]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_8, C_427)))=k3_xboole_0(A_8, C_427))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_25974])).
% 11.91/4.72  tff(c_23376, plain, (![A_12, B_13, C_427]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_427))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_427))), inference(superposition, [status(thm), theory('equality')], [c_16, c_23301])).
% 11.91/4.72  tff(c_24620, plain, (![A_450, B_451, C_452]: (k4_xboole_0(A_450, k2_xboole_0(k3_xboole_0(A_450, B_451), C_452))=k4_xboole_0(A_450, k2_xboole_0(B_451, C_452)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_23376])).
% 11.91/4.72  tff(c_24712, plain, (![C_452]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_452))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_452)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_24620])).
% 11.91/4.72  tff(c_24750, plain, (![C_452]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_452))=k4_xboole_0('#skF_4', C_452))), inference(demodulation, [status(thm), theory('equality')], [c_23383, c_24712])).
% 11.91/4.72  tff(c_28821, plain, (![A_505, C_506]: (k4_xboole_0(A_505, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_505, C_506)))=k3_xboole_0(A_505, C_506))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_25974])).
% 11.91/4.72  tff(c_28965, plain, (![C_452]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', C_452)))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_452)))), inference(superposition, [status(thm), theory('equality')], [c_24750, c_28821])).
% 11.91/4.72  tff(c_29105, plain, (![C_452]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_452))=k3_xboole_0('#skF_4', C_452))), inference(demodulation, [status(thm), theory('equality')], [c_26057, c_28965])).
% 11.91/4.72  tff(c_23127, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_23161, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_23127])).
% 11.91/4.72  tff(c_30007, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29105, c_23161])).
% 11.91/4.72  tff(c_30010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22925, c_30007])).
% 11.91/4.72  tff(c_30012, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_33])).
% 11.91/4.72  tff(c_11593, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 11.91/4.72  tff(c_22919, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_11592])).
% 11.91/4.72  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 11.91/4.72  tff(c_30056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30012, c_11593, c_22919, c_32])).
% 11.91/4.72  tff(c_30058, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 11.91/4.72  tff(c_30145, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 11.91/4.72  tff(c_30153, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_30145])).
% 11.91/4.72  tff(c_30355, plain, (![A_527, B_528, C_529]: (k4_xboole_0(k4_xboole_0(A_527, B_528), C_529)=k4_xboole_0(A_527, k2_xboole_0(B_528, C_529)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_30423, plain, (![A_527, B_528]: (k4_xboole_0(A_527, k2_xboole_0(B_528, k1_xboole_0))=k4_xboole_0(A_527, B_528))), inference(superposition, [status(thm), theory('equality')], [c_12, c_30355])).
% 11.91/4.72  tff(c_30057, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 11.91/4.72  tff(c_30072, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30057, c_4])).
% 11.91/4.72  tff(c_30159, plain, (![A_519, B_520]: (k4_xboole_0(A_519, k3_xboole_0(A_519, B_520))=k4_xboole_0(A_519, B_520))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.91/4.72  tff(c_30174, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30072, c_30159])).
% 11.91/4.72  tff(c_30185, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30174])).
% 11.91/4.72  tff(c_30233, plain, (![B_523, A_524]: (k3_xboole_0(B_523, A_524)=k1_xboole_0 | k3_xboole_0(A_524, B_523)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_4])).
% 11.91/4.72  tff(c_30251, plain, (![A_525]: (k3_xboole_0(k1_xboole_0, A_525)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_30233])).
% 11.91/4.72  tff(c_30265, plain, (![A_525]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_525))), inference(superposition, [status(thm), theory('equality')], [c_30251, c_16])).
% 11.91/4.72  tff(c_30291, plain, (![A_525]: (k4_xboole_0(k1_xboole_0, A_525)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30265])).
% 11.91/4.72  tff(c_30082, plain, (![A_515, B_516]: (k4_xboole_0(A_515, k4_xboole_0(A_515, B_516))=k3_xboole_0(A_515, B_516))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.91/4.72  tff(c_30097, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_30082])).
% 11.91/4.72  tff(c_30100, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30097])).
% 11.91/4.72  tff(c_30405, plain, (![A_8, C_529]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_529))=k4_xboole_0(k1_xboole_0, C_529))), inference(superposition, [status(thm), theory('equality')], [c_30100, c_30355])).
% 11.91/4.72  tff(c_30433, plain, (![A_8, C_529]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_529))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30291, c_30405])).
% 11.91/4.72  tff(c_30376, plain, (![A_527, B_528, B_15]: (k4_xboole_0(A_527, k2_xboole_0(B_528, k4_xboole_0(k4_xboole_0(A_527, B_528), B_15)))=k3_xboole_0(k4_xboole_0(A_527, B_528), B_15))), inference(superposition, [status(thm), theory('equality')], [c_30355, c_18])).
% 11.91/4.72  tff(c_34744, plain, (![A_608, B_609, B_610]: (k4_xboole_0(A_608, k2_xboole_0(B_609, k4_xboole_0(A_608, k2_xboole_0(B_609, B_610))))=k3_xboole_0(k4_xboole_0(A_608, B_609), B_610))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30376])).
% 11.91/4.72  tff(c_34993, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_1'))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30185, c_34744])).
% 11.91/4.72  tff(c_35068, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30433, c_2, c_34993])).
% 11.91/4.72  tff(c_30402, plain, (![A_527, B_528, B_13]: (k4_xboole_0(A_527, k2_xboole_0(B_528, k3_xboole_0(k4_xboole_0(A_527, B_528), B_13)))=k4_xboole_0(k4_xboole_0(A_527, B_528), B_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_30355])).
% 11.91/4.72  tff(c_30432, plain, (![A_527, B_528, B_13]: (k4_xboole_0(A_527, k2_xboole_0(B_528, k3_xboole_0(k4_xboole_0(A_527, B_528), B_13)))=k4_xboole_0(A_527, k2_xboole_0(B_528, B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30402])).
% 11.91/4.72  tff(c_35073, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_35068, c_30432])).
% 11.91/4.72  tff(c_35090, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30423, c_30185, c_35073])).
% 11.91/4.72  tff(c_35097, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_35090, c_35068])).
% 11.91/4.72  tff(c_35099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30153, c_35097])).
% 11.91/4.72  tff(c_35101, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 11.91/4.72  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.91/4.72  tff(c_35110, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35101, c_22])).
% 11.91/4.72  tff(c_35111, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30058, c_35110])).
% 11.91/4.72  tff(c_35119, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_35111])).
% 11.91/4.72  tff(c_35107, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_35101, c_4])).
% 11.91/4.72  tff(c_35141, plain, (![A_611, B_612]: (k4_xboole_0(A_611, k3_xboole_0(A_611, B_612))=k4_xboole_0(A_611, B_612))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.91/4.72  tff(c_35159, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35107, c_35141])).
% 11.91/4.72  tff(c_35174, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_35159])).
% 11.91/4.72  tff(c_35273, plain, (![A_617, B_618, C_619]: (k4_xboole_0(k4_xboole_0(A_617, B_618), C_619)=k4_xboole_0(A_617, k2_xboole_0(B_618, C_619)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_35769, plain, (![C_630]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_630))=k4_xboole_0('#skF_1', C_630))), inference(superposition, [status(thm), theory('equality')], [c_35174, c_35273])).
% 11.91/4.72  tff(c_36466, plain, (![B_648]: (k4_xboole_0('#skF_1', k2_xboole_0(B_648, '#skF_2'))=k4_xboole_0('#skF_1', B_648))), inference(superposition, [status(thm), theory('equality')], [c_2, c_35769])).
% 11.91/4.72  tff(c_35162, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30072, c_35141])).
% 11.91/4.72  tff(c_35175, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_35162])).
% 11.91/4.72  tff(c_36493, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_36466, c_35175])).
% 11.91/4.72  tff(c_36548, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36493, c_18])).
% 11.91/4.72  tff(c_36553, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30100, c_36548])).
% 11.91/4.72  tff(c_36555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35119, c_36553])).
% 11.91/4.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.72  
% 11.91/4.72  Inference rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Ref     : 0
% 11.91/4.72  #Sup     : 8844
% 11.91/4.72  #Fact    : 0
% 11.91/4.72  #Define  : 0
% 11.91/4.72  #Split   : 10
% 11.91/4.72  #Chain   : 0
% 11.91/4.72  #Close   : 0
% 11.91/4.72  
% 11.91/4.72  Ordering : KBO
% 11.91/4.72  
% 11.91/4.72  Simplification rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Subsume      : 39
% 11.91/4.72  #Demod        : 9564
% 11.91/4.72  #Tautology    : 5604
% 11.91/4.72  #SimpNegUnit  : 8
% 11.91/4.72  #BackRed      : 11
% 11.91/4.72  
% 11.91/4.72  #Partial instantiations: 0
% 11.91/4.72  #Strategies tried      : 1
% 11.91/4.72  
% 11.91/4.72  Timing (in seconds)
% 11.91/4.72  ----------------------
% 11.91/4.73  Preprocessing        : 0.30
% 11.91/4.73  Parsing              : 0.17
% 11.91/4.73  CNF conversion       : 0.02
% 11.91/4.73  Main loop            : 3.57
% 11.91/4.73  Inferencing          : 0.90
% 11.91/4.73  Reduction            : 1.92
% 11.91/4.73  Demodulation         : 1.64
% 11.91/4.73  BG Simplification    : 0.11
% 11.91/4.73  Subsumption          : 0.45
% 11.91/4.73  Abstraction          : 0.18
% 11.91/4.73  MUC search           : 0.00
% 11.91/4.73  Cooper               : 0.00
% 11.91/4.73  Total                : 3.99
% 11.91/4.73  Index Insertion      : 0.00
% 11.91/4.73  Index Deletion       : 0.00
% 11.91/4.73  Index Matching       : 0.00
% 11.91/4.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
