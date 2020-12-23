%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 448 expanded)
%              Number of leaves         :   29 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 582 expanded)
%              Number of equality atoms :   88 ( 385 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_32,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,(
    ! [A_44,B_45] :
      ( ~ r1_xboole_0(A_44,B_45)
      | k3_xboole_0(A_44,B_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_234,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k4_xboole_0(A_19,B_20),C_21) = k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_871,plain,(
    ! [A_66,B_67,C_68] : k4_xboole_0(k4_xboole_0(A_66,B_67),C_68) = k4_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_952,plain,(
    ! [A_22,B_23,C_68] : k4_xboole_0(A_22,k2_xboole_0(k3_xboole_0(A_22,B_23),C_68)) = k4_xboole_0(k4_xboole_0(A_22,B_23),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_871])).

tff(c_9287,plain,(
    ! [A_164,B_165,C_166] : k4_xboole_0(A_164,k2_xboole_0(k3_xboole_0(A_164,B_165),C_166)) = k4_xboole_0(A_164,k2_xboole_0(B_165,C_166)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_952])).

tff(c_9504,plain,(
    ! [C_166] : k4_xboole_0('#skF_6',k2_xboole_0(k1_xboole_0,C_166)) = k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_9287])).

tff(c_10835,plain,(
    ! [C_178] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_178)) = k4_xboole_0('#skF_6',C_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_9504])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_359,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_398,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_359])).

tff(c_408,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_398])).

tff(c_887,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k2_xboole_0(B_67,k4_xboole_0(A_66,B_67))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_408])).

tff(c_985,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(B_70,A_69)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_887])).

tff(c_1039,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_985])).

tff(c_10917,plain,(
    k4_xboole_0('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10835,c_1039])).

tff(c_1304,plain,(
    ! [A_77,B_78,C_79] : k2_xboole_0(k2_xboole_0(A_77,B_78),C_79) = k2_xboole_0(A_77,k2_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1784,plain,(
    ! [C_88,A_89,B_90] : k2_xboole_0(C_88,k2_xboole_0(A_89,B_90)) = k2_xboole_0(A_89,k2_xboole_0(B_90,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_2])).

tff(c_2179,plain,(
    ! [A_91,C_92] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_91,C_92)) = k2_xboole_0(C_92,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1784])).

tff(c_2284,plain,(
    ! [B_15,A_14] : k2_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2179])).

tff(c_2334,plain,(
    ! [B_15,A_14] : k2_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2284])).

tff(c_11046,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k2_xboole_0('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10917,c_2334])).

tff(c_11092,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_11046])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_232,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_219])).

tff(c_280,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_24])).

tff(c_285,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_280])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_547,plain,(
    ! [A_55,B_56] : k2_xboole_0(A_55,k4_xboole_0(B_56,A_55)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_587,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k4_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_547])).

tff(c_609,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_587])).

tff(c_28,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1403,plain,(
    ! [C_79] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_79) = k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_1304])).

tff(c_4245,plain,(
    ! [C_123] : k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_123)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1403])).

tff(c_4346,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_4245])).

tff(c_4383,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_4346])).

tff(c_967,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k2_xboole_0(B_67,A_66)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_887])).

tff(c_4611,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_967])).

tff(c_13153,plain,(
    ! [C_191,A_192,B_193] : k2_xboole_0(C_191,k4_xboole_0(A_192,k2_xboole_0(B_193,C_191))) = k2_xboole_0(C_191,k4_xboole_0(A_192,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_16])).

tff(c_13611,plain,(
    ! [A_195] : k2_xboole_0('#skF_6',k4_xboole_0(A_195,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_195,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_13153])).

tff(c_13725,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4611,c_13611])).

tff(c_13789,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11092,c_2,c_285,c_20,c_12,c_13725])).

tff(c_68,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_233,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_219])).

tff(c_306,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_24])).

tff(c_311,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_306])).

tff(c_13828,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_311])).

tff(c_13833,plain,(
    k2_xboole_0('#skF_5','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_37])).

tff(c_209,plain,(
    ! [A_13,C_42] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_42,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_202])).

tff(c_211,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_236,plain,(
    ! [A_46,B_47] : k4_xboole_0(k2_xboole_0(A_46,B_47),B_47) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_258,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_795,plain,(
    ! [A_64,B_65] : k4_xboole_0(k2_xboole_0(A_64,B_65),A_64) = k4_xboole_0(B_65,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_827,plain,(
    ! [B_15,A_14] : k4_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k4_xboole_0(k2_xboole_0(A_14,B_15),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_795])).

tff(c_2564,plain,(
    ! [B_94,A_95] : k4_xboole_0(k4_xboole_0(B_94,A_95),A_95) = k4_xboole_0(B_94,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_827])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2585,plain,(
    ! [B_94,A_95] : k4_xboole_0(k4_xboole_0(B_94,A_95),k4_xboole_0(B_94,A_95)) = k3_xboole_0(k4_xboole_0(B_94,A_95),A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_2564,c_26])).

tff(c_2688,plain,(
    ! [B_96,A_97] : k3_xboole_0(k4_xboole_0(B_96,A_97),A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_2585])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2696,plain,(
    ! [B_96,A_97] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_96,A_97),A_97),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_96,A_97),A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2688,c_6])).

tff(c_2791,plain,(
    ! [B_98,A_99] : r1_xboole_0(k4_xboole_0(B_98,A_99),A_99) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_2696])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2873,plain,(
    ! [A_100,B_101] : r1_xboole_0(A_100,k4_xboole_0(B_101,A_100)) ),
    inference(resolution,[status(thm)],[c_2791,c_4])).

tff(c_210,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_2955,plain,(
    ! [A_102,B_103] : k3_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2873,c_210])).

tff(c_2976,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = k4_xboole_0(A_102,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_24])).

tff(c_3051,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2976])).

tff(c_553,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),k4_xboole_0(B_56,A_55)) = k4_xboole_0(A_55,k4_xboole_0(B_56,A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_20])).

tff(c_11886,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),k4_xboole_0(B_56,A_55)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3051,c_553])).

tff(c_14477,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k4_xboole_0('#skF_3','#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13833,c_11886])).

tff(c_14577,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13828,c_20,c_285,c_14477])).

tff(c_14579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_14577])).

tff(c_14580,plain,(
    ! [A_13] : ~ r1_xboole_0(A_13,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_14582,plain,(
    ! [A_200,B_201] :
      ( ~ r1_xboole_0(A_200,B_201)
      | k3_xboole_0(A_200,B_201) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_14595,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_14582])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14602,plain,(
    ! [C_9] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14595,c_8])).

tff(c_14609,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14602])).

tff(c_15564,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_1'(A_231,B_232),k3_xboole_0(A_231,B_232))
      | r1_xboole_0(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15597,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_15564])).

tff(c_15609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14580,c_14609,c_15597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:27:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/3.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.34  
% 8.85/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.34  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 8.85/3.34  
% 8.85/3.34  %Foreground sorts:
% 8.85/3.34  
% 8.85/3.34  
% 8.85/3.34  %Background operators:
% 8.85/3.34  
% 8.85/3.34  
% 8.85/3.34  %Foreground operators:
% 8.85/3.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.85/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.85/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.85/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.85/3.34  tff('#skF_5', type, '#skF_5': $i).
% 8.85/3.34  tff('#skF_6', type, '#skF_6': $i).
% 8.85/3.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.85/3.34  tff('#skF_3', type, '#skF_3': $i).
% 8.85/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.34  tff('#skF_4', type, '#skF_4': $i).
% 8.85/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.85/3.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.85/3.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.85/3.34  
% 8.85/3.36  tff(f_80, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.85/3.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.85/3.36  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.85/3.36  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.85/3.36  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.85/3.36  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.85/3.36  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.85/3.36  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.85/3.36  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.85/3.36  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.85/3.36  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.85/3.36  tff(f_71, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.85/3.36  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.85/3.36  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.85/3.36  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.85/3.36  tff(c_83, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.85/3.36  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.85/3.36  tff(c_105, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 8.85/3.36  tff(c_32, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.85/3.36  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.85/3.36  tff(c_202, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.85/3.36  tff(c_219, plain, (![A_44, B_45]: (~r1_xboole_0(A_44, B_45) | k3_xboole_0(A_44, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_202])).
% 8.85/3.36  tff(c_234, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_219])).
% 8.85/3.36  tff(c_22, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k4_xboole_0(A_19, B_20), C_21)=k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.85/3.36  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.85/3.36  tff(c_871, plain, (![A_66, B_67, C_68]: (k4_xboole_0(k4_xboole_0(A_66, B_67), C_68)=k4_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.85/3.36  tff(c_952, plain, (![A_22, B_23, C_68]: (k4_xboole_0(A_22, k2_xboole_0(k3_xboole_0(A_22, B_23), C_68))=k4_xboole_0(k4_xboole_0(A_22, B_23), C_68))), inference(superposition, [status(thm), theory('equality')], [c_24, c_871])).
% 8.85/3.36  tff(c_9287, plain, (![A_164, B_165, C_166]: (k4_xboole_0(A_164, k2_xboole_0(k3_xboole_0(A_164, B_165), C_166))=k4_xboole_0(A_164, k2_xboole_0(B_165, C_166)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_952])).
% 8.85/3.36  tff(c_9504, plain, (![C_166]: (k4_xboole_0('#skF_6', k2_xboole_0(k1_xboole_0, C_166))=k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_166)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_9287])).
% 8.85/3.36  tff(c_10835, plain, (![C_178]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_178))=k4_xboole_0('#skF_6', C_178))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_9504])).
% 8.85/3.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.85/3.36  tff(c_36, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.85/3.36  tff(c_37, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 8.85/3.36  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.85/3.36  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.85/3.36  tff(c_18, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.85/3.36  tff(c_359, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.85/3.36  tff(c_398, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_359])).
% 8.85/3.36  tff(c_408, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_398])).
% 8.85/3.36  tff(c_887, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k2_xboole_0(B_67, k4_xboole_0(A_66, B_67)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_871, c_408])).
% 8.85/3.36  tff(c_985, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(B_70, A_69))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_887])).
% 8.85/3.36  tff(c_1039, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_985])).
% 8.85/3.36  tff(c_10917, plain, (k4_xboole_0('#skF_6', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10835, c_1039])).
% 8.85/3.36  tff(c_1304, plain, (![A_77, B_78, C_79]: (k2_xboole_0(k2_xboole_0(A_77, B_78), C_79)=k2_xboole_0(A_77, k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.85/3.36  tff(c_1784, plain, (![C_88, A_89, B_90]: (k2_xboole_0(C_88, k2_xboole_0(A_89, B_90))=k2_xboole_0(A_89, k2_xboole_0(B_90, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_1304, c_2])).
% 8.85/3.36  tff(c_2179, plain, (![A_91, C_92]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_91, C_92))=k2_xboole_0(C_92, A_91))), inference(superposition, [status(thm), theory('equality')], [c_105, c_1784])).
% 8.85/3.36  tff(c_2284, plain, (![B_15, A_14]: (k2_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2179])).
% 8.85/3.36  tff(c_2334, plain, (![B_15, A_14]: (k2_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2284])).
% 8.85/3.36  tff(c_11046, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k2_xboole_0('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10917, c_2334])).
% 8.85/3.36  tff(c_11092, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_11046])).
% 8.85/3.36  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.85/3.36  tff(c_63, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/3.36  tff(c_69, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_63])).
% 8.85/3.36  tff(c_232, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_219])).
% 8.85/3.36  tff(c_280, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_232, c_24])).
% 8.85/3.36  tff(c_285, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_280])).
% 8.85/3.36  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.85/3.36  tff(c_547, plain, (![A_55, B_56]: (k2_xboole_0(A_55, k4_xboole_0(B_56, A_55))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.85/3.36  tff(c_587, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k4_xboole_0(A_17, B_18))=k2_xboole_0(B_18, k2_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_547])).
% 8.85/3.36  tff(c_609, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k2_xboole_0(A_17, B_18))=k2_xboole_0(B_18, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_587])).
% 8.85/3.36  tff(c_28, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.85/3.36  tff(c_1403, plain, (![C_79]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_79)=k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_79)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_1304])).
% 8.85/3.36  tff(c_4245, plain, (![C_123]: (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_123))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_123)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1403])).
% 8.85/3.36  tff(c_4346, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_609, c_4245])).
% 8.85/3.36  tff(c_4383, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_4346])).
% 8.85/3.36  tff(c_967, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k2_xboole_0(B_67, A_66))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_887])).
% 8.85/3.36  tff(c_4611, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4383, c_967])).
% 8.85/3.36  tff(c_13153, plain, (![C_191, A_192, B_193]: (k2_xboole_0(C_191, k4_xboole_0(A_192, k2_xboole_0(B_193, C_191)))=k2_xboole_0(C_191, k4_xboole_0(A_192, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_871, c_16])).
% 8.85/3.36  tff(c_13611, plain, (![A_195]: (k2_xboole_0('#skF_6', k4_xboole_0(A_195, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_195, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_37, c_13153])).
% 8.85/3.36  tff(c_13725, plain, (k2_xboole_0('#skF_6', k4_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4611, c_13611])).
% 8.85/3.36  tff(c_13789, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11092, c_2, c_285, c_20, c_12, c_13725])).
% 8.85/3.36  tff(c_68, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_63])).
% 8.85/3.36  tff(c_233, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_219])).
% 8.85/3.36  tff(c_306, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_233, c_24])).
% 8.85/3.36  tff(c_311, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_306])).
% 8.85/3.36  tff(c_13828, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_311])).
% 8.85/3.36  tff(c_13833, plain, (k2_xboole_0('#skF_5', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_37])).
% 8.85/3.36  tff(c_209, plain, (![A_13, C_42]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_202])).
% 8.85/3.36  tff(c_211, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_209])).
% 8.85/3.36  tff(c_236, plain, (![A_46, B_47]: (k4_xboole_0(k2_xboole_0(A_46, B_47), B_47)=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.85/3.36  tff(c_258, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_236])).
% 8.85/3.36  tff(c_795, plain, (![A_64, B_65]: (k4_xboole_0(k2_xboole_0(A_64, B_65), A_64)=k4_xboole_0(B_65, A_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_236])).
% 8.85/3.36  tff(c_827, plain, (![B_15, A_14]: (k4_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k4_xboole_0(k2_xboole_0(A_14, B_15), A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_795])).
% 8.85/3.36  tff(c_2564, plain, (![B_94, A_95]: (k4_xboole_0(k4_xboole_0(B_94, A_95), A_95)=k4_xboole_0(B_94, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_827])).
% 8.85/3.36  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.85/3.36  tff(c_2585, plain, (![B_94, A_95]: (k4_xboole_0(k4_xboole_0(B_94, A_95), k4_xboole_0(B_94, A_95))=k3_xboole_0(k4_xboole_0(B_94, A_95), A_95))), inference(superposition, [status(thm), theory('equality')], [c_2564, c_26])).
% 8.85/3.36  tff(c_2688, plain, (![B_96, A_97]: (k3_xboole_0(k4_xboole_0(B_96, A_97), A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_408, c_2585])).
% 8.85/3.36  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.85/3.36  tff(c_2696, plain, (![B_96, A_97]: (r2_hidden('#skF_1'(k4_xboole_0(B_96, A_97), A_97), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_96, A_97), A_97))), inference(superposition, [status(thm), theory('equality')], [c_2688, c_6])).
% 8.85/3.36  tff(c_2791, plain, (![B_98, A_99]: (r1_xboole_0(k4_xboole_0(B_98, A_99), A_99))), inference(negUnitSimplification, [status(thm)], [c_211, c_2696])).
% 8.85/3.36  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/3.36  tff(c_2873, plain, (![A_100, B_101]: (r1_xboole_0(A_100, k4_xboole_0(B_101, A_100)))), inference(resolution, [status(thm)], [c_2791, c_4])).
% 8.85/3.36  tff(c_210, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_202])).
% 8.85/3.36  tff(c_2955, plain, (![A_102, B_103]: (k3_xboole_0(A_102, k4_xboole_0(B_103, A_102))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2873, c_210])).
% 8.85/3.36  tff(c_2976, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(B_103, A_102))=k4_xboole_0(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2955, c_24])).
% 8.85/3.36  tff(c_3051, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(B_103, A_102))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2976])).
% 8.85/3.36  tff(c_553, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), k4_xboole_0(B_56, A_55))=k4_xboole_0(A_55, k4_xboole_0(B_56, A_55)))), inference(superposition, [status(thm), theory('equality')], [c_547, c_20])).
% 8.85/3.36  tff(c_11886, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), k4_xboole_0(B_56, A_55))=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_3051, c_553])).
% 8.85/3.36  tff(c_14477, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k4_xboole_0('#skF_3', '#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13833, c_11886])).
% 8.85/3.36  tff(c_14577, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13828, c_20, c_285, c_14477])).
% 8.85/3.36  tff(c_14579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_14577])).
% 8.85/3.36  tff(c_14580, plain, (![A_13]: (~r1_xboole_0(A_13, k1_xboole_0))), inference(splitRight, [status(thm)], [c_209])).
% 8.85/3.36  tff(c_14582, plain, (![A_200, B_201]: (~r1_xboole_0(A_200, B_201) | k3_xboole_0(A_200, B_201)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_202])).
% 8.85/3.36  tff(c_14595, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_14582])).
% 8.85/3.36  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.85/3.36  tff(c_14602, plain, (![C_9]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14595, c_8])).
% 8.85/3.36  tff(c_14609, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14602])).
% 8.85/3.36  tff(c_15564, plain, (![A_231, B_232]: (r2_hidden('#skF_1'(A_231, B_232), k3_xboole_0(A_231, B_232)) | r1_xboole_0(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.85/3.36  tff(c_15597, plain, (![A_13]: (r2_hidden('#skF_1'(A_13, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_15564])).
% 8.85/3.36  tff(c_15609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14580, c_14609, c_15597])).
% 8.85/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.36  
% 8.85/3.36  Inference rules
% 8.85/3.36  ----------------------
% 8.85/3.36  #Ref     : 0
% 8.85/3.36  #Sup     : 3936
% 8.85/3.36  #Fact    : 0
% 8.85/3.36  #Define  : 0
% 8.85/3.36  #Split   : 1
% 8.85/3.36  #Chain   : 0
% 8.85/3.36  #Close   : 0
% 8.85/3.36  
% 8.85/3.36  Ordering : KBO
% 8.85/3.36  
% 8.85/3.36  Simplification rules
% 8.85/3.36  ----------------------
% 8.85/3.36  #Subsume      : 81
% 8.85/3.36  #Demod        : 4524
% 8.85/3.36  #Tautology    : 2268
% 8.85/3.36  #SimpNegUnit  : 21
% 8.85/3.36  #BackRed      : 43
% 8.85/3.36  
% 8.85/3.36  #Partial instantiations: 0
% 8.85/3.36  #Strategies tried      : 1
% 8.85/3.36  
% 8.85/3.36  Timing (in seconds)
% 8.85/3.36  ----------------------
% 8.85/3.37  Preprocessing        : 0.31
% 8.85/3.37  Parsing              : 0.17
% 8.85/3.37  CNF conversion       : 0.02
% 8.85/3.37  Main loop            : 2.27
% 8.85/3.37  Inferencing          : 0.45
% 8.85/3.37  Reduction            : 1.35
% 8.85/3.37  Demodulation         : 1.21
% 8.85/3.37  BG Simplification    : 0.06
% 8.85/3.37  Subsumption          : 0.29
% 8.85/3.37  Abstraction          : 0.09
% 8.85/3.37  MUC search           : 0.00
% 8.85/3.37  Cooper               : 0.00
% 8.85/3.37  Total                : 2.62
% 8.85/3.37  Index Insertion      : 0.00
% 8.85/3.37  Index Deletion       : 0.00
% 8.85/3.37  Index Matching       : 0.00
% 8.85/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
