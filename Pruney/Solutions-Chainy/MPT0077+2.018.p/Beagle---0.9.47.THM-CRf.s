%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 898 expanded)
%              Number of leaves         :   23 ( 303 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 (1231 expanded)
%              Number of equality atoms :  158 ( 730 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_144,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_148,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [B_18,A_19] : k2_xboole_0(B_18,A_19) = k2_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_19] : k2_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_8])).

tff(c_149,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_67])).

tff(c_165,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = B_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_156])).

tff(c_6919,plain,(
    ! [A_158,B_159] : k4_xboole_0(A_158,k4_xboole_0(A_158,B_159)) = k3_xboole_0(A_158,B_159) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6943,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k3_xboole_0(B_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_6919])).

tff(c_6951,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6943])).

tff(c_220,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_244,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k3_xboole_0(B_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_220])).

tff(c_252,plain,(
    ! [B_26] : k4_xboole_0(B_26,B_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_244])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_302,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_4])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_199,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_203,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_16])).

tff(c_210,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_207])).

tff(c_399,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k4_xboole_0(A_37,B_38),C_39) = k4_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_882,plain,(
    ! [C_52] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_52)) = k4_xboole_0('#skF_4',C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_399])).

tff(c_898,plain,(
    ! [C_52] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_52)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_18])).

tff(c_933,plain,(
    ! [C_52] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_52)) = k3_xboole_0('#skF_4',C_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_898])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_28])).

tff(c_327,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_360,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_1184,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_360])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_1184])).

tff(c_1188,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_1222,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1188,c_4])).

tff(c_1230,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_16])).

tff(c_1233,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1230])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1255,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k4_xboole_0(A_58,B_59),C_60) = k4_xboole_0(A_58,k2_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1265,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(B_59,k4_xboole_0(A_58,B_59))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_252])).

tff(c_1356,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k2_xboole_0(B_62,A_61)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1265])).

tff(c_1371,plain,(
    ! [B_62,A_61] : k2_xboole_0(k2_xboole_0(B_62,A_61),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_62,A_61),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_1356,c_12])).

tff(c_5319,plain,(
    ! [B_123,A_124] : k2_xboole_0(k2_xboole_0(B_123,A_124),A_124) = k2_xboole_0(B_123,A_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2,c_1371])).

tff(c_1292,plain,(
    ! [C_60] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_60)) = k4_xboole_0('#skF_1',C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_1255])).

tff(c_5356,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5319,c_1292])).

tff(c_5453,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_5356])).

tff(c_5502,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5453,c_18])).

tff(c_5514,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_5502])).

tff(c_5516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5514])).

tff(c_5517,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_5560,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5517,c_4])).

tff(c_5644,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_16])).

tff(c_5647,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_5644])).

tff(c_5561,plain,(
    ! [A_126,B_127,C_128] : k4_xboole_0(k4_xboole_0(A_126,B_127),C_128) = k4_xboole_0(A_126,k2_xboole_0(B_127,C_128)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5571,plain,(
    ! [A_126,B_127] : k4_xboole_0(A_126,k2_xboole_0(B_127,k4_xboole_0(A_126,B_127))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5561,c_252])).

tff(c_5664,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k2_xboole_0(B_130,A_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5571])).

tff(c_5679,plain,(
    ! [B_130,A_129] : k2_xboole_0(k2_xboole_0(B_130,A_129),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_130,A_129),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_5664,c_12])).

tff(c_6638,plain,(
    ! [B_153,A_154] : k2_xboole_0(k2_xboole_0(B_153,A_154),A_154) = k2_xboole_0(B_153,A_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2,c_5679])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5615,plain,(
    ! [A_12,B_13,C_128] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_128)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5561])).

tff(c_6161,plain,(
    ! [A_144,B_145,C_146] : k4_xboole_0(A_144,k2_xboole_0(k3_xboole_0(A_144,B_145),C_146)) = k4_xboole_0(A_144,k2_xboole_0(B_145,C_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5615])).

tff(c_6217,plain,(
    ! [C_146] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_146)) = k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_6161])).

tff(c_6267,plain,(
    ! [C_146] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_146)) = k4_xboole_0('#skF_1',C_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_6217])).

tff(c_6651,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6638,c_6267])).

tff(c_6717,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5647,c_6651])).

tff(c_6882,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6717,c_18])).

tff(c_6890,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_6882])).

tff(c_6892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_6890])).

tff(c_6893,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6902,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6893,c_4])).

tff(c_6906,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6902,c_16])).

tff(c_6909,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_6906])).

tff(c_7104,plain,(
    ! [A_167,B_168,C_169] : k4_xboole_0(k4_xboole_0(A_167,B_168),C_169) = k4_xboole_0(A_167,k2_xboole_0(B_168,C_169)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7117,plain,(
    ! [A_167,B_168] : k4_xboole_0(A_167,k2_xboole_0(B_168,k4_xboole_0(A_167,B_168))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7104,c_6951])).

tff(c_7188,plain,(
    ! [A_170,B_171] : k4_xboole_0(A_170,k2_xboole_0(B_171,A_170)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7117])).

tff(c_7206,plain,(
    ! [B_171,A_170] : k2_xboole_0(k2_xboole_0(B_171,A_170),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_171,A_170),A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_7188,c_12])).

tff(c_8019,plain,(
    ! [B_189,A_190] : k2_xboole_0(k2_xboole_0(B_189,A_190),A_190) = k2_xboole_0(B_189,A_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2,c_7206])).

tff(c_7158,plain,(
    ! [C_169] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_169)) = k4_xboole_0('#skF_1',C_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_6909,c_7104])).

tff(c_8045,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8019,c_7158])).

tff(c_8105,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6909,c_8045])).

tff(c_8131,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8105,c_18])).

tff(c_8140,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6951,c_8131])).

tff(c_8142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_8140])).

tff(c_8144,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8150,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8144,c_26])).

tff(c_8151,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8150])).

tff(c_8155,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_8151])).

tff(c_11837,plain,(
    ! [A_286,B_287] : k2_xboole_0(A_286,k4_xboole_0(B_287,A_286)) = k2_xboole_0(A_286,B_287) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11844,plain,(
    ! [B_287] : k4_xboole_0(B_287,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_11837,c_67])).

tff(c_11859,plain,(
    ! [B_287] : k4_xboole_0(B_287,k1_xboole_0) = B_287 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_11844])).

tff(c_11888,plain,(
    ! [A_289,B_290] : k4_xboole_0(A_289,k4_xboole_0(A_289,B_290)) = k3_xboole_0(A_289,B_290) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11909,plain,(
    ! [B_287] : k4_xboole_0(B_287,B_287) = k3_xboole_0(B_287,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11859,c_11888])).

tff(c_11919,plain,(
    ! [B_287] : k4_xboole_0(B_287,B_287) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11909])).

tff(c_8148,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8144,c_4])).

tff(c_8160,plain,(
    ! [A_191,B_192] : k4_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k4_xboole_0(A_191,B_192) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8169,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8148,c_8160])).

tff(c_11864,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11859,c_8169])).

tff(c_12101,plain,(
    ! [A_298,B_299,C_300] : k4_xboole_0(k4_xboole_0(A_298,B_299),C_300) = k4_xboole_0(A_298,k2_xboole_0(B_299,C_300)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12561,plain,(
    ! [C_311] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_311)) = k4_xboole_0('#skF_1',C_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_11864,c_12101])).

tff(c_12621,plain,(
    ! [B_312] : k4_xboole_0('#skF_1',k2_xboole_0(B_312,'#skF_2')) = k4_xboole_0('#skF_1',B_312) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_12561])).

tff(c_10897,plain,(
    ! [A_260,B_261] : k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = k2_xboole_0(A_260,B_261) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10904,plain,(
    ! [B_261] : k4_xboole_0(B_261,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_10897,c_67])).

tff(c_10934,plain,(
    ! [B_262] : k4_xboole_0(B_262,k1_xboole_0) = B_262 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10904])).

tff(c_10943,plain,(
    ! [B_262] : k4_xboole_0(B_262,B_262) = k3_xboole_0(B_262,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10934,c_18])).

tff(c_10949,plain,(
    ! [B_262] : k4_xboole_0(B_262,B_262) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10943])).

tff(c_10925,plain,(
    ! [B_261] : k4_xboole_0(B_261,k1_xboole_0) = B_261 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10904])).

tff(c_10933,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10925,c_8169])).

tff(c_11003,plain,(
    ! [A_264,B_265,C_266] : k4_xboole_0(k4_xboole_0(A_264,B_265),C_266) = k4_xboole_0(A_264,k2_xboole_0(B_265,C_266)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11607,plain,(
    ! [C_283] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_283)) = k4_xboole_0('#skF_1',C_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_10933,c_11003])).

tff(c_11723,plain,(
    ! [A_285] : k4_xboole_0('#skF_1',k2_xboole_0(A_285,'#skF_2')) = k4_xboole_0('#skF_1',A_285) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11607])).

tff(c_8217,plain,(
    ! [A_193,B_194] : k2_xboole_0(A_193,k4_xboole_0(B_194,A_193)) = k2_xboole_0(A_193,B_194) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8224,plain,(
    ! [B_194] : k4_xboole_0(B_194,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_8217,c_67])).

tff(c_8245,plain,(
    ! [B_194] : k4_xboole_0(B_194,k1_xboole_0) = B_194 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_8224])).

tff(c_9837,plain,(
    ! [A_232,B_233] : k4_xboole_0(A_232,k4_xboole_0(A_232,B_233)) = k3_xboole_0(A_232,B_233) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9864,plain,(
    ! [B_194] : k4_xboole_0(B_194,B_194) = k3_xboole_0(B_194,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8245,c_9837])).

tff(c_9876,plain,(
    ! [B_194] : k4_xboole_0(B_194,B_194) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9864])).

tff(c_8253,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8245,c_8169])).

tff(c_9992,plain,(
    ! [A_237,B_238,C_239] : k4_xboole_0(k4_xboole_0(A_237,B_238),C_239) = k4_xboole_0(A_237,k2_xboole_0(B_238,C_239)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10109,plain,(
    ! [C_240] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_240)) = k4_xboole_0('#skF_1',C_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_8253,c_9992])).

tff(c_10756,plain,(
    ! [A_257] : k4_xboole_0('#skF_1',k2_xboole_0(A_257,'#skF_2')) = k4_xboole_0('#skF_1',A_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10109])).

tff(c_8176,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_8180,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8176,c_4])).

tff(c_8192,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_8196,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8192,c_4])).

tff(c_8200,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8196,c_16])).

tff(c_8252,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8245,c_8200])).

tff(c_8448,plain,(
    ! [A_201,B_202,C_203] : k4_xboole_0(k4_xboole_0(A_201,B_202),C_203) = k4_xboole_0(A_201,k2_xboole_0(B_202,C_203)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8962,plain,(
    ! [C_217] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_217)) = k4_xboole_0('#skF_4',C_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_8252,c_8448])).

tff(c_8975,plain,(
    ! [C_217] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_217)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8962,c_18])).

tff(c_9009,plain,(
    ! [C_217] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_217)) = k3_xboole_0('#skF_4',C_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8975])).

tff(c_8276,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_8297,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_8276])).

tff(c_9796,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9009,c_8297])).

tff(c_9799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8180,c_9796])).

tff(c_9800,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_9824,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9800,c_4])).

tff(c_9832,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9824,c_16])).

tff(c_9835,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8245,c_9832])).

tff(c_10773,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10756,c_9835])).

tff(c_10836,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10773,c_18])).

tff(c_10843,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_10836])).

tff(c_10845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8155,c_10843])).

tff(c_10846,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10855,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10846,c_4])).

tff(c_10859,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10855,c_16])).

tff(c_10862,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8169,c_10859])).

tff(c_11343,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10933,c_10862])).

tff(c_11737,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11723,c_11343])).

tff(c_11806,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11737,c_18])).

tff(c_11811,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10949,c_11806])).

tff(c_11813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8155,c_11811])).

tff(c_11814,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_11823,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11814,c_4])).

tff(c_11827,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11823,c_16])).

tff(c_12355,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11859,c_11827])).

tff(c_12635,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12621,c_12355])).

tff(c_12701,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12635,c_18])).

tff(c_12708,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11919,c_12701])).

tff(c_12710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8155,c_12708])).

tff(c_12711,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8150])).

tff(c_12716,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12711,c_4])).

tff(c_12744,plain,(
    ! [A_313,B_314] : k2_xboole_0(A_313,k4_xboole_0(B_314,A_313)) = k2_xboole_0(A_313,B_314) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12751,plain,(
    ! [B_314] : k4_xboole_0(B_314,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_314) ),
    inference(superposition,[status(thm),theory(equality)],[c_12744,c_67])).

tff(c_12760,plain,(
    ! [B_314] : k4_xboole_0(B_314,k1_xboole_0) = B_314 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_12751])).

tff(c_12712,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_8150])).

tff(c_8143,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_12734,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12712,c_8143])).

tff(c_12738,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12734,c_4])).

tff(c_12778,plain,(
    ! [A_316,B_317] : k4_xboole_0(A_316,k3_xboole_0(A_316,B_317)) = k4_xboole_0(A_316,B_317) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12790,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12738,c_12778])).

tff(c_12806,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12760,c_12790])).

tff(c_12893,plain,(
    ! [A_320,B_321,C_322] : k4_xboole_0(k4_xboole_0(A_320,B_321),C_322) = k4_xboole_0(A_320,k2_xboole_0(B_321,C_322)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13596,plain,(
    ! [C_341] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_341)) = k4_xboole_0('#skF_4',C_341) ),
    inference(superposition,[status(thm),theory(equality)],[c_12806,c_12893])).

tff(c_13612,plain,(
    ! [C_341] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_341)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_341)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_18])).

tff(c_13647,plain,(
    ! [C_341] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_341)) = k3_xboole_0('#skF_4',C_341) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_13612])).

tff(c_12827,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_12847,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_12827])).

tff(c_14035,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13647,c_12847])).

tff(c_14038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12716,c_14035])).

tff(c_14040,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_33])).

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

tff(c_14136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14040,c_8144,c_12712,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.54  
% 7.00/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.55  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.00/2.55  
% 7.00/2.55  %Foreground sorts:
% 7.00/2.55  
% 7.00/2.55  
% 7.00/2.55  %Background operators:
% 7.00/2.55  
% 7.00/2.55  
% 7.00/2.55  %Foreground operators:
% 7.00/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.00/2.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.00/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.00/2.55  tff('#skF_5', type, '#skF_5': $i).
% 7.00/2.55  tff('#skF_6', type, '#skF_6': $i).
% 7.00/2.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.00/2.55  tff('#skF_2', type, '#skF_2': $i).
% 7.00/2.55  tff('#skF_3', type, '#skF_3': $i).
% 7.00/2.55  tff('#skF_1', type, '#skF_1': $i).
% 7.00/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.00/2.55  tff('#skF_4', type, '#skF_4': $i).
% 7.00/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.00/2.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.00/2.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.00/2.55  
% 7.00/2.57  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.00/2.57  tff(f_60, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.00/2.57  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.00/2.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.00/2.57  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.00/2.57  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.00/2.57  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.00/2.57  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.00/2.57  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.00/2.57  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.00/2.57  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.57  tff(c_144, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 7.00/2.57  tff(c_148, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_144])).
% 7.00/2.57  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.00/2.57  tff(c_51, plain, (![B_18, A_19]: (k2_xboole_0(B_18, A_19)=k2_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.00/2.57  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.00/2.57  tff(c_67, plain, (![A_19]: (k2_xboole_0(k1_xboole_0, A_19)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_51, c_8])).
% 7.00/2.57  tff(c_149, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.57  tff(c_156, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_26))), inference(superposition, [status(thm), theory('equality')], [c_149, c_67])).
% 7.00/2.57  tff(c_165, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=B_26)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_156])).
% 7.00/2.57  tff(c_6919, plain, (![A_158, B_159]: (k4_xboole_0(A_158, k4_xboole_0(A_158, B_159))=k3_xboole_0(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.00/2.57  tff(c_6943, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k3_xboole_0(B_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_6919])).
% 7.00/2.57  tff(c_6951, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6943])).
% 7.00/2.57  tff(c_220, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.00/2.57  tff(c_244, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k3_xboole_0(B_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_220])).
% 7.00/2.57  tff(c_252, plain, (![B_26]: (k4_xboole_0(B_26, B_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_244])).
% 7.00/2.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.00/2.57  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.57  tff(c_31, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 7.00/2.57  tff(c_302, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 7.00/2.57  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.00/2.57  tff(c_306, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_4])).
% 7.00/2.57  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.00/2.57  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.57  tff(c_34, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 7.00/2.57  tff(c_199, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 7.00/2.57  tff(c_203, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_199, c_4])).
% 7.00/2.57  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.00/2.57  tff(c_207, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_203, c_16])).
% 7.00/2.57  tff(c_210, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_207])).
% 7.00/2.57  tff(c_399, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k4_xboole_0(A_37, B_38), C_39)=k4_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.57  tff(c_882, plain, (![C_52]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_52))=k4_xboole_0('#skF_4', C_52))), inference(superposition, [status(thm), theory('equality')], [c_210, c_399])).
% 7.00/2.57  tff(c_898, plain, (![C_52]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_52))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_52)))), inference(superposition, [status(thm), theory('equality')], [c_882, c_18])).
% 7.00/2.57  tff(c_933, plain, (![C_52]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_52))=k3_xboole_0('#skF_4', C_52))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_898])).
% 7.00/2.57  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.57  tff(c_33, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_28])).
% 7.00/2.57  tff(c_327, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 7.00/2.57  tff(c_360, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_327])).
% 7.00/2.57  tff(c_1184, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_933, c_360])).
% 7.00/2.57  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_1184])).
% 7.00/2.57  tff(c_1188, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 7.00/2.57  tff(c_1222, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1188, c_4])).
% 7.00/2.57  tff(c_1230, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1222, c_16])).
% 7.00/2.57  tff(c_1233, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1230])).
% 7.00/2.57  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.57  tff(c_1255, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k4_xboole_0(A_58, B_59), C_60)=k4_xboole_0(A_58, k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.57  tff(c_1265, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(B_59, k4_xboole_0(A_58, B_59)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1255, c_252])).
% 7.00/2.57  tff(c_1356, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k2_xboole_0(B_62, A_61))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1265])).
% 7.00/2.57  tff(c_1371, plain, (![B_62, A_61]: (k2_xboole_0(k2_xboole_0(B_62, A_61), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_62, A_61), A_61))), inference(superposition, [status(thm), theory('equality')], [c_1356, c_12])).
% 7.00/2.57  tff(c_5319, plain, (![B_123, A_124]: (k2_xboole_0(k2_xboole_0(B_123, A_124), A_124)=k2_xboole_0(B_123, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2, c_1371])).
% 7.00/2.57  tff(c_1292, plain, (![C_60]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_60))=k4_xboole_0('#skF_1', C_60))), inference(superposition, [status(thm), theory('equality')], [c_1233, c_1255])).
% 7.00/2.57  tff(c_5356, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5319, c_1292])).
% 7.00/2.57  tff(c_5453, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_5356])).
% 7.00/2.57  tff(c_5502, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5453, c_18])).
% 7.00/2.57  tff(c_5514, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_252, c_5502])).
% 7.00/2.57  tff(c_5516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_5514])).
% 7.00/2.57  tff(c_5517, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 7.00/2.57  tff(c_5560, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5517, c_4])).
% 7.00/2.57  tff(c_5644, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5560, c_16])).
% 7.00/2.57  tff(c_5647, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_5644])).
% 7.00/2.57  tff(c_5561, plain, (![A_126, B_127, C_128]: (k4_xboole_0(k4_xboole_0(A_126, B_127), C_128)=k4_xboole_0(A_126, k2_xboole_0(B_127, C_128)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.57  tff(c_5571, plain, (![A_126, B_127]: (k4_xboole_0(A_126, k2_xboole_0(B_127, k4_xboole_0(A_126, B_127)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5561, c_252])).
% 7.00/2.57  tff(c_5664, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k2_xboole_0(B_130, A_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5571])).
% 7.00/2.57  tff(c_5679, plain, (![B_130, A_129]: (k2_xboole_0(k2_xboole_0(B_130, A_129), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_130, A_129), A_129))), inference(superposition, [status(thm), theory('equality')], [c_5664, c_12])).
% 7.00/2.57  tff(c_6638, plain, (![B_153, A_154]: (k2_xboole_0(k2_xboole_0(B_153, A_154), A_154)=k2_xboole_0(B_153, A_154))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2, c_5679])).
% 7.00/2.57  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.57  tff(c_5615, plain, (![A_12, B_13, C_128]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_128))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_128))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5561])).
% 7.00/2.57  tff(c_6161, plain, (![A_144, B_145, C_146]: (k4_xboole_0(A_144, k2_xboole_0(k3_xboole_0(A_144, B_145), C_146))=k4_xboole_0(A_144, k2_xboole_0(B_145, C_146)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5615])).
% 7.00/2.57  tff(c_6217, plain, (![C_146]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_146))=k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_5560, c_6161])).
% 7.00/2.57  tff(c_6267, plain, (![C_146]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_146))=k4_xboole_0('#skF_1', C_146))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_6217])).
% 7.00/2.57  tff(c_6651, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6638, c_6267])).
% 7.00/2.57  tff(c_6717, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5647, c_6651])).
% 7.00/2.57  tff(c_6882, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6717, c_18])).
% 7.00/2.57  tff(c_6890, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_252, c_6882])).
% 7.00/2.57  tff(c_6892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_6890])).
% 7.00/2.57  tff(c_6893, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 7.00/2.57  tff(c_6902, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_6893, c_4])).
% 7.00/2.57  tff(c_6906, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6902, c_16])).
% 7.00/2.57  tff(c_6909, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_6906])).
% 7.00/2.58  tff(c_7104, plain, (![A_167, B_168, C_169]: (k4_xboole_0(k4_xboole_0(A_167, B_168), C_169)=k4_xboole_0(A_167, k2_xboole_0(B_168, C_169)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_7117, plain, (![A_167, B_168]: (k4_xboole_0(A_167, k2_xboole_0(B_168, k4_xboole_0(A_167, B_168)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7104, c_6951])).
% 7.00/2.58  tff(c_7188, plain, (![A_170, B_171]: (k4_xboole_0(A_170, k2_xboole_0(B_171, A_170))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7117])).
% 7.00/2.58  tff(c_7206, plain, (![B_171, A_170]: (k2_xboole_0(k2_xboole_0(B_171, A_170), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_171, A_170), A_170))), inference(superposition, [status(thm), theory('equality')], [c_7188, c_12])).
% 7.00/2.58  tff(c_8019, plain, (![B_189, A_190]: (k2_xboole_0(k2_xboole_0(B_189, A_190), A_190)=k2_xboole_0(B_189, A_190))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2, c_7206])).
% 7.00/2.58  tff(c_7158, plain, (![C_169]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_169))=k4_xboole_0('#skF_1', C_169))), inference(superposition, [status(thm), theory('equality')], [c_6909, c_7104])).
% 7.00/2.58  tff(c_8045, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8019, c_7158])).
% 7.00/2.58  tff(c_8105, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6909, c_8045])).
% 7.00/2.58  tff(c_8131, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8105, c_18])).
% 7.00/2.58  tff(c_8140, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6951, c_8131])).
% 7.00/2.58  tff(c_8142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_8140])).
% 7.00/2.58  tff(c_8144, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 7.00/2.58  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.58  tff(c_8150, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8144, c_26])).
% 7.00/2.58  tff(c_8151, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_8150])).
% 7.00/2.58  tff(c_8155, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_8151])).
% 7.00/2.58  tff(c_11837, plain, (![A_286, B_287]: (k2_xboole_0(A_286, k4_xboole_0(B_287, A_286))=k2_xboole_0(A_286, B_287))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.58  tff(c_11844, plain, (![B_287]: (k4_xboole_0(B_287, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_287))), inference(superposition, [status(thm), theory('equality')], [c_11837, c_67])).
% 7.00/2.58  tff(c_11859, plain, (![B_287]: (k4_xboole_0(B_287, k1_xboole_0)=B_287)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_11844])).
% 7.00/2.58  tff(c_11888, plain, (![A_289, B_290]: (k4_xboole_0(A_289, k4_xboole_0(A_289, B_290))=k3_xboole_0(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.00/2.58  tff(c_11909, plain, (![B_287]: (k4_xboole_0(B_287, B_287)=k3_xboole_0(B_287, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11859, c_11888])).
% 7.00/2.58  tff(c_11919, plain, (![B_287]: (k4_xboole_0(B_287, B_287)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11909])).
% 7.00/2.58  tff(c_8148, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_8144, c_4])).
% 7.00/2.58  tff(c_8160, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k4_xboole_0(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.00/2.58  tff(c_8169, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8148, c_8160])).
% 7.00/2.58  tff(c_11864, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11859, c_8169])).
% 7.00/2.58  tff(c_12101, plain, (![A_298, B_299, C_300]: (k4_xboole_0(k4_xboole_0(A_298, B_299), C_300)=k4_xboole_0(A_298, k2_xboole_0(B_299, C_300)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_12561, plain, (![C_311]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_311))=k4_xboole_0('#skF_1', C_311))), inference(superposition, [status(thm), theory('equality')], [c_11864, c_12101])).
% 7.00/2.58  tff(c_12621, plain, (![B_312]: (k4_xboole_0('#skF_1', k2_xboole_0(B_312, '#skF_2'))=k4_xboole_0('#skF_1', B_312))), inference(superposition, [status(thm), theory('equality')], [c_2, c_12561])).
% 7.00/2.58  tff(c_10897, plain, (![A_260, B_261]: (k2_xboole_0(A_260, k4_xboole_0(B_261, A_260))=k2_xboole_0(A_260, B_261))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.58  tff(c_10904, plain, (![B_261]: (k4_xboole_0(B_261, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_261))), inference(superposition, [status(thm), theory('equality')], [c_10897, c_67])).
% 7.00/2.58  tff(c_10934, plain, (![B_262]: (k4_xboole_0(B_262, k1_xboole_0)=B_262)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10904])).
% 7.00/2.58  tff(c_10943, plain, (![B_262]: (k4_xboole_0(B_262, B_262)=k3_xboole_0(B_262, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10934, c_18])).
% 7.00/2.58  tff(c_10949, plain, (![B_262]: (k4_xboole_0(B_262, B_262)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10943])).
% 7.00/2.58  tff(c_10925, plain, (![B_261]: (k4_xboole_0(B_261, k1_xboole_0)=B_261)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10904])).
% 7.00/2.58  tff(c_10933, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10925, c_8169])).
% 7.00/2.58  tff(c_11003, plain, (![A_264, B_265, C_266]: (k4_xboole_0(k4_xboole_0(A_264, B_265), C_266)=k4_xboole_0(A_264, k2_xboole_0(B_265, C_266)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_11607, plain, (![C_283]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_283))=k4_xboole_0('#skF_1', C_283))), inference(superposition, [status(thm), theory('equality')], [c_10933, c_11003])).
% 7.00/2.58  tff(c_11723, plain, (![A_285]: (k4_xboole_0('#skF_1', k2_xboole_0(A_285, '#skF_2'))=k4_xboole_0('#skF_1', A_285))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11607])).
% 7.00/2.58  tff(c_8217, plain, (![A_193, B_194]: (k2_xboole_0(A_193, k4_xboole_0(B_194, A_193))=k2_xboole_0(A_193, B_194))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.58  tff(c_8224, plain, (![B_194]: (k4_xboole_0(B_194, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_194))), inference(superposition, [status(thm), theory('equality')], [c_8217, c_67])).
% 7.00/2.58  tff(c_8245, plain, (![B_194]: (k4_xboole_0(B_194, k1_xboole_0)=B_194)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_8224])).
% 7.00/2.58  tff(c_9837, plain, (![A_232, B_233]: (k4_xboole_0(A_232, k4_xboole_0(A_232, B_233))=k3_xboole_0(A_232, B_233))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.00/2.58  tff(c_9864, plain, (![B_194]: (k4_xboole_0(B_194, B_194)=k3_xboole_0(B_194, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8245, c_9837])).
% 7.00/2.58  tff(c_9876, plain, (![B_194]: (k4_xboole_0(B_194, B_194)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9864])).
% 7.00/2.58  tff(c_8253, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8245, c_8169])).
% 7.00/2.58  tff(c_9992, plain, (![A_237, B_238, C_239]: (k4_xboole_0(k4_xboole_0(A_237, B_238), C_239)=k4_xboole_0(A_237, k2_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_10109, plain, (![C_240]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_240))=k4_xboole_0('#skF_1', C_240))), inference(superposition, [status(thm), theory('equality')], [c_8253, c_9992])).
% 7.00/2.58  tff(c_10756, plain, (![A_257]: (k4_xboole_0('#skF_1', k2_xboole_0(A_257, '#skF_2'))=k4_xboole_0('#skF_1', A_257))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10109])).
% 7.00/2.58  tff(c_8176, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_31])).
% 7.00/2.58  tff(c_8180, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8176, c_4])).
% 7.00/2.58  tff(c_8192, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 7.00/2.58  tff(c_8196, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_8192, c_4])).
% 7.00/2.58  tff(c_8200, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8196, c_16])).
% 7.00/2.58  tff(c_8252, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8245, c_8200])).
% 7.00/2.58  tff(c_8448, plain, (![A_201, B_202, C_203]: (k4_xboole_0(k4_xboole_0(A_201, B_202), C_203)=k4_xboole_0(A_201, k2_xboole_0(B_202, C_203)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_8962, plain, (![C_217]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_217))=k4_xboole_0('#skF_4', C_217))), inference(superposition, [status(thm), theory('equality')], [c_8252, c_8448])).
% 7.00/2.58  tff(c_8975, plain, (![C_217]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_217))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_217)))), inference(superposition, [status(thm), theory('equality')], [c_8962, c_18])).
% 7.00/2.58  tff(c_9009, plain, (![C_217]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_217))=k3_xboole_0('#skF_4', C_217))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8975])).
% 7.00/2.58  tff(c_8276, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 7.00/2.58  tff(c_8297, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_8276])).
% 7.00/2.58  tff(c_9796, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9009, c_8297])).
% 7.00/2.58  tff(c_9799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8180, c_9796])).
% 7.00/2.58  tff(c_9800, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_33])).
% 7.00/2.58  tff(c_9824, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_9800, c_4])).
% 7.00/2.58  tff(c_9832, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9824, c_16])).
% 7.00/2.58  tff(c_9835, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8245, c_9832])).
% 7.00/2.58  tff(c_10773, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10756, c_9835])).
% 7.00/2.58  tff(c_10836, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10773, c_18])).
% 7.00/2.58  tff(c_10843, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_10836])).
% 7.00/2.58  tff(c_10845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8155, c_10843])).
% 7.00/2.58  tff(c_10846, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 7.00/2.58  tff(c_10855, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10846, c_4])).
% 7.00/2.58  tff(c_10859, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10855, c_16])).
% 7.00/2.58  tff(c_10862, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8169, c_10859])).
% 7.00/2.58  tff(c_11343, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10933, c_10862])).
% 7.00/2.58  tff(c_11737, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11723, c_11343])).
% 7.00/2.58  tff(c_11806, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11737, c_18])).
% 7.00/2.58  tff(c_11811, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10949, c_11806])).
% 7.00/2.58  tff(c_11813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8155, c_11811])).
% 7.00/2.58  tff(c_11814, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 7.00/2.58  tff(c_11823, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11814, c_4])).
% 7.00/2.58  tff(c_11827, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11823, c_16])).
% 7.00/2.58  tff(c_12355, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11859, c_11827])).
% 7.00/2.58  tff(c_12635, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12621, c_12355])).
% 7.00/2.58  tff(c_12701, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12635, c_18])).
% 7.00/2.58  tff(c_12708, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11919, c_12701])).
% 7.00/2.58  tff(c_12710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8155, c_12708])).
% 7.00/2.58  tff(c_12711, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_8150])).
% 7.00/2.58  tff(c_12716, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_12711, c_4])).
% 7.00/2.58  tff(c_12744, plain, (![A_313, B_314]: (k2_xboole_0(A_313, k4_xboole_0(B_314, A_313))=k2_xboole_0(A_313, B_314))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.58  tff(c_12751, plain, (![B_314]: (k4_xboole_0(B_314, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_314))), inference(superposition, [status(thm), theory('equality')], [c_12744, c_67])).
% 7.00/2.58  tff(c_12760, plain, (![B_314]: (k4_xboole_0(B_314, k1_xboole_0)=B_314)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_12751])).
% 7.00/2.58  tff(c_12712, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_8150])).
% 7.00/2.58  tff(c_8143, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 7.00/2.58  tff(c_12734, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12712, c_8143])).
% 7.00/2.58  tff(c_12738, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12734, c_4])).
% 7.00/2.58  tff(c_12778, plain, (![A_316, B_317]: (k4_xboole_0(A_316, k3_xboole_0(A_316, B_317))=k4_xboole_0(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.00/2.58  tff(c_12790, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12738, c_12778])).
% 7.00/2.58  tff(c_12806, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12760, c_12790])).
% 7.00/2.58  tff(c_12893, plain, (![A_320, B_321, C_322]: (k4_xboole_0(k4_xboole_0(A_320, B_321), C_322)=k4_xboole_0(A_320, k2_xboole_0(B_321, C_322)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.58  tff(c_13596, plain, (![C_341]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_341))=k4_xboole_0('#skF_4', C_341))), inference(superposition, [status(thm), theory('equality')], [c_12806, c_12893])).
% 7.00/2.58  tff(c_13612, plain, (![C_341]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_341))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_341)))), inference(superposition, [status(thm), theory('equality')], [c_13596, c_18])).
% 7.00/2.58  tff(c_13647, plain, (![C_341]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_341))=k3_xboole_0('#skF_4', C_341))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_13612])).
% 7.00/2.58  tff(c_12827, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_33])).
% 7.00/2.58  tff(c_12847, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_12827])).
% 7.00/2.58  tff(c_14035, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13647, c_12847])).
% 7.00/2.58  tff(c_14038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12716, c_14035])).
% 7.00/2.58  tff(c_14040, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_33])).
% 7.00/2.58  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.00/2.58  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 7.00/2.58  tff(c_14136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14040, c_8144, c_12712, c_32])).
% 7.00/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.58  
% 7.00/2.58  Inference rules
% 7.00/2.58  ----------------------
% 7.00/2.58  #Ref     : 0
% 7.00/2.58  #Sup     : 3397
% 7.00/2.58  #Fact    : 0
% 7.00/2.58  #Define  : 0
% 7.00/2.58  #Split   : 10
% 7.00/2.58  #Chain   : 0
% 7.00/2.58  #Close   : 0
% 7.00/2.58  
% 7.00/2.58  Ordering : KBO
% 7.00/2.58  
% 7.00/2.58  Simplification rules
% 7.00/2.58  ----------------------
% 7.00/2.58  #Subsume      : 13
% 7.00/2.58  #Demod        : 3378
% 7.00/2.58  #Tautology    : 2418
% 7.00/2.58  #SimpNegUnit  : 6
% 7.00/2.58  #BackRed      : 12
% 7.00/2.58  
% 7.00/2.58  #Partial instantiations: 0
% 7.00/2.58  #Strategies tried      : 1
% 7.00/2.58  
% 7.00/2.58  Timing (in seconds)
% 7.00/2.58  ----------------------
% 7.36/2.58  Preprocessing        : 0.27
% 7.36/2.58  Parsing              : 0.15
% 7.36/2.58  CNF conversion       : 0.02
% 7.36/2.58  Main loop            : 1.50
% 7.36/2.58  Inferencing          : 0.46
% 7.36/2.58  Reduction            : 0.72
% 7.36/2.58  Demodulation         : 0.60
% 7.36/2.58  BG Simplification    : 0.05
% 7.36/2.58  Subsumption          : 0.18
% 7.36/2.58  Abstraction          : 0.08
% 7.36/2.58  MUC search           : 0.00
% 7.36/2.58  Cooper               : 0.00
% 7.36/2.58  Total                : 1.84
% 7.36/2.58  Index Insertion      : 0.00
% 7.36/2.58  Index Deletion       : 0.00
% 7.36/2.58  Index Matching       : 0.00
% 7.36/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
