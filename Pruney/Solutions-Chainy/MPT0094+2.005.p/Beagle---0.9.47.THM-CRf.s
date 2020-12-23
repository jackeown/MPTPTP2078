%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 12.66s
% Output     : CNFRefutation 12.76s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 372 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :   74 ( 365 expanded)
%              Number of equality atoms :   69 ( 359 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_129,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_507,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k4_xboole_0(A_42,B_43),k3_xboole_0(A_42,C_44)) = k4_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_558,plain,(
    ! [A_3,B_43] : k4_xboole_0(A_3,k4_xboole_0(B_43,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_43),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_507])).

tff(c_569,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_558])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_576,plain,(
    ! [A_45] : k4_xboole_0(A_45,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_6])).

tff(c_606,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_576])).

tff(c_567,plain,(
    ! [A_3,B_43] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_3,B_43)) = k4_xboole_0(A_3,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_558])).

tff(c_242,plain,(
    ! [A_33,C_34,B_35] : k2_xboole_0(k4_xboole_0(A_33,C_34),k4_xboole_0(B_35,C_34)) = k4_xboole_0(k2_xboole_0(A_33,B_35),C_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_276,plain,(
    ! [A_33,A_6] : k4_xboole_0(k2_xboole_0(A_33,A_6),A_6) = k2_xboole_0(k4_xboole_0(A_33,A_6),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_242])).

tff(c_305,plain,(
    ! [A_33,A_6] : k4_xboole_0(k2_xboole_0(A_33,A_6),A_6) = k2_xboole_0(k1_xboole_0,k4_xboole_0(A_33,A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_276])).

tff(c_1022,plain,(
    ! [A_57,A_58] : k4_xboole_0(k2_xboole_0(A_57,A_58),A_58) = k4_xboole_0(A_57,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_305])).

tff(c_1072,plain,(
    ! [A_45] : k4_xboole_0(k1_xboole_0,A_45) = k4_xboole_0(A_45,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_1022])).

tff(c_1107,plain,(
    ! [A_45] : k4_xboole_0(k1_xboole_0,A_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1072])).

tff(c_561,plain,(
    ! [A_6,C_44] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_44)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_507])).

tff(c_1112,plain,(
    ! [A_6,C_44] : k2_xboole_0(A_6,k3_xboole_0(A_6,C_44)) = k4_xboole_0(A_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_561])).

tff(c_1114,plain,(
    ! [A_6,C_44] : k2_xboole_0(A_6,k3_xboole_0(A_6,C_44)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1112])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)) = k4_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1222,plain,(
    ! [B_61,C_62,A_63] : k2_xboole_0(k4_xboole_0(B_61,C_62),k4_xboole_0(A_63,C_62)) = k4_xboole_0(k2_xboole_0(A_63,B_61),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] : k2_xboole_0(k4_xboole_0(A_7,C_9),k4_xboole_0(B_8,C_9)) = k4_xboole_0(k2_xboole_0(A_7,B_8),C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8206,plain,(
    ! [B_148,A_149,C_150] : k4_xboole_0(k2_xboole_0(B_148,A_149),C_150) = k4_xboole_0(k2_xboole_0(A_149,B_148),C_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_10])).

tff(c_9029,plain,(
    ! [B_153,A_154] : k4_xboole_0(k2_xboole_0(B_153,A_154),k1_xboole_0) = k2_xboole_0(A_154,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_8206,c_8])).

tff(c_9194,plain,(
    ! [A_4,B_5] : k4_xboole_0(k2_xboole_0(A_4,B_5),k1_xboole_0) = k2_xboole_0(k4_xboole_0(B_5,A_4),A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_9029])).

tff(c_10381,plain,(
    ! [B_163,A_164] : k2_xboole_0(k4_xboole_0(B_163,A_164),A_164) = k2_xboole_0(A_164,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9194])).

tff(c_10565,plain,(
    ! [A_12,C_14] : k4_xboole_0(A_12,k4_xboole_0(k3_xboole_0(A_12,C_14),C_14)) = k2_xboole_0(k3_xboole_0(A_12,C_14),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_10381])).

tff(c_10643,plain,(
    ! [A_12,C_14] : k4_xboole_0(A_12,k4_xboole_0(k3_xboole_0(A_12,C_14),C_14)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_2,c_10565])).

tff(c_11042,plain,(
    ! [A_168,C_169] : k4_xboole_0(A_168,k4_xboole_0(k3_xboole_0(A_168,C_169),C_169)) = A_168 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_2,c_10565])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    ! [A_33,A_10,B_11] : k2_xboole_0(k4_xboole_0(A_33,k4_xboole_0(A_10,B_11)),k3_xboole_0(A_10,B_11)) = k4_xboole_0(k2_xboole_0(A_33,A_10),k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_242])).

tff(c_11089,plain,(
    ! [A_168,C_169] : k4_xboole_0(k2_xboole_0(A_168,k3_xboole_0(A_168,C_169)),k4_xboole_0(k3_xboole_0(A_168,C_169),C_169)) = k2_xboole_0(A_168,k3_xboole_0(k3_xboole_0(A_168,C_169),C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11042,c_282])).

tff(c_11299,plain,(
    ! [A_168,C_169] : k2_xboole_0(A_168,k3_xboole_0(k3_xboole_0(A_168,C_169),C_169)) = A_168 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_1114,c_11089])).

tff(c_113,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(k4_xboole_0(A_27,B_28),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_2044,plain,(
    ! [A_79,B_80] : k2_xboole_0(k4_xboole_0(A_79,B_80),k3_xboole_0(A_79,B_80)) = k2_xboole_0(A_79,k4_xboole_0(A_79,B_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_2056,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(B_80,B_80)) = k2_xboole_0(A_79,k4_xboole_0(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_14])).

tff(c_2144,plain,(
    ! [A_79,B_80] : k2_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129,c_2056])).

tff(c_1293,plain,(
    ! [A_6,B_61] : k4_xboole_0(k2_xboole_0(A_6,B_61),A_6) = k2_xboole_0(k4_xboole_0(B_61,A_6),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1222])).

tff(c_1559,plain,(
    ! [A_70,B_71] : k4_xboole_0(k2_xboole_0(A_70,B_71),A_70) = k4_xboole_0(B_71,A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_2,c_1293])).

tff(c_1594,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = k2_xboole_0(A_70,k2_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_6])).

tff(c_2776,plain,(
    ! [A_91,B_92] : k2_xboole_0(A_91,k2_xboole_0(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1594])).

tff(c_568,plain,(
    ! [A_33,A_6] : k4_xboole_0(k2_xboole_0(A_33,A_6),A_6) = k4_xboole_0(A_33,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_305])).

tff(c_2795,plain,(
    ! [A_91,B_92] : k4_xboole_0(k2_xboole_0(A_91,B_92),k2_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,k2_xboole_0(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2776,c_568])).

tff(c_2890,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k2_xboole_0(A_93,B_94)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_2795])).

tff(c_2940,plain,(
    ! [A_93,B_94] : k3_xboole_0(A_93,k2_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_12])).

tff(c_3026,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k2_xboole_0(A_95,B_96)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2940])).

tff(c_519,plain,(
    ! [A_42,C_44,B_43] : k2_xboole_0(k3_xboole_0(A_42,C_44),k4_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_2])).

tff(c_3053,plain,(
    ! [A_95,B_43,B_96] : k4_xboole_0(A_95,k4_xboole_0(B_43,k2_xboole_0(A_95,B_96))) = k2_xboole_0(A_95,k4_xboole_0(A_95,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3026,c_519])).

tff(c_12896,plain,(
    ! [A_184,B_185,B_186] : k4_xboole_0(A_184,k4_xboole_0(B_185,k2_xboole_0(A_184,B_186))) = A_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_3053])).

tff(c_13358,plain,(
    ! [A_187,B_188] : k4_xboole_0(A_187,k4_xboole_0(B_188,A_187)) = A_187 ),
    inference(superposition,[status(thm),theory(equality)],[c_11299,c_12896])).

tff(c_13696,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_13358])).

tff(c_294,plain,(
    ! [B_35,C_34,A_33] : k2_xboole_0(k4_xboole_0(B_35,C_34),k4_xboole_0(A_33,C_34)) = k4_xboole_0(k2_xboole_0(A_33,B_35),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_13840,plain,(
    ! [A_33] : k4_xboole_0(k2_xboole_0(A_33,'#skF_2'),'#skF_1') = k2_xboole_0('#skF_2',k4_xboole_0(A_33,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13696,c_294])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') != k2_xboole_0(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') != k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_15876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13840,c_23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.66/5.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.76/5.07  
% 12.76/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.76/5.08  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.76/5.08  
% 12.76/5.08  %Foreground sorts:
% 12.76/5.08  
% 12.76/5.08  
% 12.76/5.08  %Background operators:
% 12.76/5.08  
% 12.76/5.08  
% 12.76/5.08  %Foreground operators:
% 12.76/5.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.76/5.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.76/5.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.76/5.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.76/5.08  tff('#skF_2', type, '#skF_2': $i).
% 12.76/5.08  tff('#skF_3', type, '#skF_3': $i).
% 12.76/5.08  tff('#skF_1', type, '#skF_1': $i).
% 12.76/5.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.76/5.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.76/5.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.76/5.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.76/5.08  
% 12.76/5.10  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 12.76/5.10  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.76/5.10  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.76/5.10  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 12.76/5.10  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.76/5.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.76/5.10  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 12.76/5.10  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.76/5.10  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 12.76/5.10  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.76/5.10  tff(c_73, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.76/5.10  tff(c_77, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_73])).
% 12.76/5.10  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.76/5.10  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.76/5.10  tff(c_104, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.76/5.10  tff(c_125, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_104])).
% 12.76/5.10  tff(c_129, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 12.76/5.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.76/5.10  tff(c_507, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k4_xboole_0(A_42, B_43), k3_xboole_0(A_42, C_44))=k4_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.76/5.10  tff(c_558, plain, (![A_3, B_43]: (k4_xboole_0(A_3, k4_xboole_0(B_43, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_43), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_507])).
% 12.76/5.10  tff(c_569, plain, (![A_45, B_46]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_558])).
% 12.76/5.10  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.76/5.10  tff(c_576, plain, (![A_45]: (k4_xboole_0(A_45, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_45))), inference(superposition, [status(thm), theory('equality')], [c_569, c_6])).
% 12.76/5.10  tff(c_606, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_576])).
% 12.76/5.10  tff(c_567, plain, (![A_3, B_43]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_3, B_43))=k4_xboole_0(A_3, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_558])).
% 12.76/5.10  tff(c_242, plain, (![A_33, C_34, B_35]: (k2_xboole_0(k4_xboole_0(A_33, C_34), k4_xboole_0(B_35, C_34))=k4_xboole_0(k2_xboole_0(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.76/5.10  tff(c_276, plain, (![A_33, A_6]: (k4_xboole_0(k2_xboole_0(A_33, A_6), A_6)=k2_xboole_0(k4_xboole_0(A_33, A_6), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_242])).
% 12.76/5.10  tff(c_305, plain, (![A_33, A_6]: (k4_xboole_0(k2_xboole_0(A_33, A_6), A_6)=k2_xboole_0(k1_xboole_0, k4_xboole_0(A_33, A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_276])).
% 12.76/5.10  tff(c_1022, plain, (![A_57, A_58]: (k4_xboole_0(k2_xboole_0(A_57, A_58), A_58)=k4_xboole_0(A_57, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_305])).
% 12.76/5.10  tff(c_1072, plain, (![A_45]: (k4_xboole_0(k1_xboole_0, A_45)=k4_xboole_0(A_45, A_45))), inference(superposition, [status(thm), theory('equality')], [c_606, c_1022])).
% 12.76/5.10  tff(c_1107, plain, (![A_45]: (k4_xboole_0(k1_xboole_0, A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1072])).
% 12.76/5.10  tff(c_561, plain, (![A_6, C_44]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_44))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_507])).
% 12.76/5.10  tff(c_1112, plain, (![A_6, C_44]: (k2_xboole_0(A_6, k3_xboole_0(A_6, C_44))=k4_xboole_0(A_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_561])).
% 12.76/5.10  tff(c_1114, plain, (![A_6, C_44]: (k2_xboole_0(A_6, k3_xboole_0(A_6, C_44))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1112])).
% 12.76/5.10  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14))=k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.76/5.10  tff(c_1222, plain, (![B_61, C_62, A_63]: (k2_xboole_0(k4_xboole_0(B_61, C_62), k4_xboole_0(A_63, C_62))=k4_xboole_0(k2_xboole_0(A_63, B_61), C_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 12.76/5.10  tff(c_10, plain, (![A_7, C_9, B_8]: (k2_xboole_0(k4_xboole_0(A_7, C_9), k4_xboole_0(B_8, C_9))=k4_xboole_0(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.76/5.10  tff(c_8206, plain, (![B_148, A_149, C_150]: (k4_xboole_0(k2_xboole_0(B_148, A_149), C_150)=k4_xboole_0(k2_xboole_0(A_149, B_148), C_150))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_10])).
% 12.76/5.10  tff(c_9029, plain, (![B_153, A_154]: (k4_xboole_0(k2_xboole_0(B_153, A_154), k1_xboole_0)=k2_xboole_0(A_154, B_153))), inference(superposition, [status(thm), theory('equality')], [c_8206, c_8])).
% 12.76/5.10  tff(c_9194, plain, (![A_4, B_5]: (k4_xboole_0(k2_xboole_0(A_4, B_5), k1_xboole_0)=k2_xboole_0(k4_xboole_0(B_5, A_4), A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_9029])).
% 12.76/5.10  tff(c_10381, plain, (![B_163, A_164]: (k2_xboole_0(k4_xboole_0(B_163, A_164), A_164)=k2_xboole_0(A_164, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9194])).
% 12.76/5.10  tff(c_10565, plain, (![A_12, C_14]: (k4_xboole_0(A_12, k4_xboole_0(k3_xboole_0(A_12, C_14), C_14))=k2_xboole_0(k3_xboole_0(A_12, C_14), A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_10381])).
% 12.76/5.10  tff(c_10643, plain, (![A_12, C_14]: (k4_xboole_0(A_12, k4_xboole_0(k3_xboole_0(A_12, C_14), C_14))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_2, c_10565])).
% 12.76/5.10  tff(c_11042, plain, (![A_168, C_169]: (k4_xboole_0(A_168, k4_xboole_0(k3_xboole_0(A_168, C_169), C_169))=A_168)), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_2, c_10565])).
% 12.76/5.10  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.76/5.10  tff(c_282, plain, (![A_33, A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_33, k4_xboole_0(A_10, B_11)), k3_xboole_0(A_10, B_11))=k4_xboole_0(k2_xboole_0(A_33, A_10), k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_242])).
% 12.76/5.10  tff(c_11089, plain, (![A_168, C_169]: (k4_xboole_0(k2_xboole_0(A_168, k3_xboole_0(A_168, C_169)), k4_xboole_0(k3_xboole_0(A_168, C_169), C_169))=k2_xboole_0(A_168, k3_xboole_0(k3_xboole_0(A_168, C_169), C_169)))), inference(superposition, [status(thm), theory('equality')], [c_11042, c_282])).
% 12.76/5.10  tff(c_11299, plain, (![A_168, C_169]: (k2_xboole_0(A_168, k3_xboole_0(k3_xboole_0(A_168, C_169), C_169))=A_168)), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_1114, c_11089])).
% 12.76/5.10  tff(c_113, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(k4_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 12.76/5.10  tff(c_2044, plain, (![A_79, B_80]: (k2_xboole_0(k4_xboole_0(A_79, B_80), k3_xboole_0(A_79, B_80))=k2_xboole_0(A_79, k4_xboole_0(A_79, B_80)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_113])).
% 12.76/5.10  tff(c_2056, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(B_80, B_80))=k2_xboole_0(A_79, k4_xboole_0(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_2044, c_14])).
% 12.76/5.10  tff(c_2144, plain, (![A_79, B_80]: (k2_xboole_0(A_79, k4_xboole_0(A_79, B_80))=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129, c_2056])).
% 12.76/5.10  tff(c_1293, plain, (![A_6, B_61]: (k4_xboole_0(k2_xboole_0(A_6, B_61), A_6)=k2_xboole_0(k4_xboole_0(B_61, A_6), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_1222])).
% 12.76/5.10  tff(c_1559, plain, (![A_70, B_71]: (k4_xboole_0(k2_xboole_0(A_70, B_71), A_70)=k4_xboole_0(B_71, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_2, c_1293])).
% 12.76/5.10  tff(c_1594, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k4_xboole_0(B_71, A_70))=k2_xboole_0(A_70, k2_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_6])).
% 12.76/5.10  tff(c_2776, plain, (![A_91, B_92]: (k2_xboole_0(A_91, k2_xboole_0(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1594])).
% 12.76/5.10  tff(c_568, plain, (![A_33, A_6]: (k4_xboole_0(k2_xboole_0(A_33, A_6), A_6)=k4_xboole_0(A_33, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_305])).
% 12.76/5.10  tff(c_2795, plain, (![A_91, B_92]: (k4_xboole_0(k2_xboole_0(A_91, B_92), k2_xboole_0(A_91, B_92))=k4_xboole_0(A_91, k2_xboole_0(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_2776, c_568])).
% 12.76/5.10  tff(c_2890, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k2_xboole_0(A_93, B_94))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_2795])).
% 12.76/5.10  tff(c_2940, plain, (![A_93, B_94]: (k3_xboole_0(A_93, k2_xboole_0(A_93, B_94))=k4_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_12])).
% 12.76/5.10  tff(c_3026, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k2_xboole_0(A_95, B_96))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2940])).
% 12.76/5.10  tff(c_519, plain, (![A_42, C_44, B_43]: (k2_xboole_0(k3_xboole_0(A_42, C_44), k4_xboole_0(A_42, B_43))=k4_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_507, c_2])).
% 12.76/5.10  tff(c_3053, plain, (![A_95, B_43, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_43, k2_xboole_0(A_95, B_96)))=k2_xboole_0(A_95, k4_xboole_0(A_95, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_3026, c_519])).
% 12.76/5.10  tff(c_12896, plain, (![A_184, B_185, B_186]: (k4_xboole_0(A_184, k4_xboole_0(B_185, k2_xboole_0(A_184, B_186)))=A_184)), inference(demodulation, [status(thm), theory('equality')], [c_2144, c_3053])).
% 12.76/5.10  tff(c_13358, plain, (![A_187, B_188]: (k4_xboole_0(A_187, k4_xboole_0(B_188, A_187))=A_187)), inference(superposition, [status(thm), theory('equality')], [c_11299, c_12896])).
% 12.76/5.10  tff(c_13696, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_77, c_13358])).
% 12.76/5.10  tff(c_294, plain, (![B_35, C_34, A_33]: (k2_xboole_0(k4_xboole_0(B_35, C_34), k4_xboole_0(A_33, C_34))=k4_xboole_0(k2_xboole_0(A_33, B_35), C_34))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 12.76/5.10  tff(c_13840, plain, (![A_33]: (k4_xboole_0(k2_xboole_0(A_33, '#skF_2'), '#skF_1')=k2_xboole_0('#skF_2', k4_xboole_0(A_33, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_13696, c_294])).
% 12.76/5.10  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k2_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.76/5.10  tff(c_23, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 12.76/5.10  tff(c_15876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13840, c_23])).
% 12.76/5.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.76/5.10  
% 12.76/5.10  Inference rules
% 12.76/5.10  ----------------------
% 12.76/5.10  #Ref     : 0
% 12.76/5.10  #Sup     : 3969
% 12.76/5.10  #Fact    : 0
% 12.76/5.10  #Define  : 0
% 12.76/5.10  #Split   : 0
% 12.76/5.10  #Chain   : 0
% 12.76/5.11  #Close   : 0
% 12.76/5.11  
% 12.76/5.11  Ordering : KBO
% 12.76/5.11  
% 12.76/5.11  Simplification rules
% 12.76/5.11  ----------------------
% 12.76/5.11  #Subsume      : 46
% 12.76/5.11  #Demod        : 5204
% 12.76/5.11  #Tautology    : 2711
% 12.76/5.11  #SimpNegUnit  : 0
% 12.76/5.11  #BackRed      : 10
% 12.76/5.11  
% 12.76/5.11  #Partial instantiations: 0
% 12.76/5.11  #Strategies tried      : 1
% 12.76/5.11  
% 12.76/5.11  Timing (in seconds)
% 12.76/5.11  ----------------------
% 12.76/5.11  Preprocessing        : 0.45
% 12.76/5.11  Parsing              : 0.24
% 12.76/5.11  CNF conversion       : 0.03
% 12.76/5.11  Main loop            : 3.70
% 12.76/5.11  Inferencing          : 0.79
% 12.76/5.11  Reduction            : 2.12
% 12.76/5.11  Demodulation         : 1.88
% 12.76/5.11  BG Simplification    : 0.11
% 12.76/5.11  Subsumption          : 0.48
% 12.76/5.11  Abstraction          : 0.17
% 12.76/5.11  MUC search           : 0.00
% 12.76/5.11  Cooper               : 0.00
% 12.76/5.11  Total                : 4.21
% 12.76/5.11  Index Insertion      : 0.00
% 12.76/5.11  Index Deletion       : 0.00
% 12.76/5.11  Index Matching       : 0.00
% 12.76/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
