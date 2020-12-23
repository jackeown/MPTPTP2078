%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 523 expanded)
%              Number of leaves         :   29 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          :  103 ( 640 expanded)
%              Number of equality atoms :   89 ( 503 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_12])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_238,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1303,plain,(
    ! [A_68,B_69] :
      ( ~ r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_238])).

tff(c_1316,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1303])).

tff(c_1367,plain,(
    ! [A_70,B_71] : k2_xboole_0(k3_xboole_0(A_70,B_71),k4_xboole_0(A_70,B_71)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1379,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_1367])).

tff(c_1679,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_72])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1496,plain,(
    ! [A_74,B_75] : k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1505,plain,(
    ! [B_75,A_74] : k2_xboole_0(B_75,k4_xboole_0(A_74,B_75)) = k2_xboole_0(B_75,k2_xboole_0(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_14])).

tff(c_1552,plain,(
    ! [B_75,A_74] : k2_xboole_0(B_75,k2_xboole_0(A_74,B_75)) = k2_xboole_0(B_75,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1505])).

tff(c_36,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_37,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_2180,plain,(
    ! [A_83,B_84,C_85] : k2_xboole_0(k2_xboole_0(A_83,B_84),C_85) = k2_xboole_0(A_83,k2_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2200,plain,(
    ! [C_85,A_83,B_84] : k2_xboole_0(C_85,k2_xboole_0(A_83,B_84)) = k2_xboole_0(A_83,k2_xboole_0(B_84,C_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2180,c_2])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1754,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1767,plain,(
    ! [A_78,B_79] : k2_xboole_0(k3_xboole_0(A_78,B_79),k4_xboole_0(A_78,B_79)) = k2_xboole_0(k3_xboole_0(A_78,B_79),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_14])).

tff(c_2335,plain,(
    ! [A_86,B_87] : k2_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_1767])).

tff(c_2428,plain,(
    ! [B_88] : k3_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2335,c_72])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2452,plain,(
    ! [B_88] : k3_xboole_0(B_88,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2428,c_4])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_198,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_213,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_198])).

tff(c_2833,plain,(
    ! [A_97] : k4_xboole_0(A_97,A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_213])).

tff(c_2867,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(B_19,k4_xboole_0(A_18,B_19))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2833])).

tff(c_3225,plain,(
    ! [A_108,B_109] : k4_xboole_0(A_108,k2_xboole_0(B_109,A_108)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2867])).

tff(c_3285,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_3225])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2251,plain,(
    ! [C_85] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_85) = k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_2180])).

tff(c_2287,plain,(
    ! [C_85] : k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_85)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2251])).

tff(c_4259,plain,(
    ! [B_128,A_129] : k2_xboole_0(B_128,k2_xboole_0(A_129,B_128)) = k2_xboole_0(B_128,A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1505])).

tff(c_4321,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2287,c_4259])).

tff(c_4382,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_4321])).

tff(c_32,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1315,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1303])).

tff(c_1792,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_1754])).

tff(c_1812,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1792])).

tff(c_1957,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k4_xboole_0(A_80,B_81),C_82) = k4_xboole_0(A_80,k2_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5494,plain,(
    ! [C_144] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_144)) = k4_xboole_0('#skF_6',C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_1957])).

tff(c_5534,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4382,c_5494])).

tff(c_5592,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3285,c_5534])).

tff(c_6264,plain,(
    k2_xboole_0(k2_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k2_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5592,c_14])).

tff(c_6275,plain,(
    k2_xboole_0('#skF_3','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1552,c_37,c_2200,c_2,c_72,c_2,c_6264])).

tff(c_1542,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1496])).

tff(c_7623,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_1542])).

tff(c_7645,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_18,c_7623])).

tff(c_1351,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1316])).

tff(c_1783,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_1754])).

tff(c_1809,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1783])).

tff(c_7638,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_18])).

tff(c_7650,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_7638])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_201,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_24])).

tff(c_5286,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_201])).

tff(c_1804,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_1767])).

tff(c_5565,plain,(
    ! [B_79] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_4',B_79)) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1804,c_5494])).

tff(c_6278,plain,(
    ! [B_148] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_4',B_148)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_5565])).

tff(c_6314,plain,(
    ! [B_39] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_4',B_39)) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5286,c_6278])).

tff(c_7658,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7645,c_6314])).

tff(c_155,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_37])).

tff(c_1530,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_1496])).

tff(c_8079,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7658,c_1530])).

tff(c_11562,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7650,c_8079])).

tff(c_11607,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11562,c_1315])).

tff(c_1394,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1367])).

tff(c_11920,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11607,c_1394])).

tff(c_11966,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7645,c_11920])).

tff(c_11968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_11966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.82  
% 7.71/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.82  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.71/2.82  
% 7.71/2.82  %Foreground sorts:
% 7.71/2.82  
% 7.71/2.82  
% 7.71/2.82  %Background operators:
% 7.71/2.82  
% 7.71/2.82  
% 7.71/2.82  %Foreground operators:
% 7.71/2.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.71/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.71/2.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.71/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.71/2.82  tff('#skF_5', type, '#skF_5': $i).
% 7.71/2.82  tff('#skF_6', type, '#skF_6': $i).
% 7.71/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.71/2.82  tff('#skF_3', type, '#skF_3': $i).
% 7.71/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.82  tff('#skF_4', type, '#skF_4': $i).
% 7.71/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.71/2.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.71/2.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.71/2.82  
% 7.71/2.84  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 7.71/2.84  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.71/2.84  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.71/2.84  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.71/2.84  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.71/2.84  tff(f_69, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.71/2.84  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.71/2.84  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.71/2.84  tff(f_67, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.71/2.84  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.71/2.84  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.71/2.84  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.71/2.84  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.71/2.84  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.71/2.84  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.84  tff(c_56, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.71/2.84  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.71/2.84  tff(c_72, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_56, c_12])).
% 7.71/2.84  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.84  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.71/2.84  tff(c_238, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.71/2.84  tff(c_1303, plain, (![A_68, B_69]: (~r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_238])).
% 7.71/2.84  tff(c_1316, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1303])).
% 7.71/2.84  tff(c_1367, plain, (![A_70, B_71]: (k2_xboole_0(k3_xboole_0(A_70, B_71), k4_xboole_0(A_70, B_71))=A_70)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.71/2.84  tff(c_1379, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1316, c_1367])).
% 7.71/2.84  tff(c_1679, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1379, c_72])).
% 7.71/2.84  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.84  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.71/2.84  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.71/2.84  tff(c_1496, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.71/2.84  tff(c_1505, plain, (![B_75, A_74]: (k2_xboole_0(B_75, k4_xboole_0(A_74, B_75))=k2_xboole_0(B_75, k2_xboole_0(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_14])).
% 7.71/2.84  tff(c_1552, plain, (![B_75, A_74]: (k2_xboole_0(B_75, k2_xboole_0(A_74, B_75))=k2_xboole_0(B_75, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1505])).
% 7.71/2.84  tff(c_36, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.84  tff(c_37, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 7.71/2.84  tff(c_2180, plain, (![A_83, B_84, C_85]: (k2_xboole_0(k2_xboole_0(A_83, B_84), C_85)=k2_xboole_0(A_83, k2_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.71/2.84  tff(c_2200, plain, (![C_85, A_83, B_84]: (k2_xboole_0(C_85, k2_xboole_0(A_83, B_84))=k2_xboole_0(A_83, k2_xboole_0(B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_2180, c_2])).
% 7.71/2.84  tff(c_20, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.71/2.84  tff(c_28, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.71/2.84  tff(c_1754, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.71/2.84  tff(c_1767, plain, (![A_78, B_79]: (k2_xboole_0(k3_xboole_0(A_78, B_79), k4_xboole_0(A_78, B_79))=k2_xboole_0(k3_xboole_0(A_78, B_79), A_78))), inference(superposition, [status(thm), theory('equality')], [c_1754, c_14])).
% 7.71/2.84  tff(c_2335, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k3_xboole_0(A_86, B_87))=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_1767])).
% 7.71/2.84  tff(c_2428, plain, (![B_88]: (k3_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2335, c_72])).
% 7.71/2.84  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.71/2.84  tff(c_2452, plain, (![B_88]: (k3_xboole_0(B_88, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2428, c_4])).
% 7.71/2.84  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.71/2.84  tff(c_198, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.71/2.84  tff(c_213, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_198])).
% 7.71/2.84  tff(c_2833, plain, (![A_97]: (k4_xboole_0(A_97, A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_213])).
% 7.71/2.84  tff(c_2867, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(B_19, k4_xboole_0(A_18, B_19)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2833])).
% 7.71/2.84  tff(c_3225, plain, (![A_108, B_109]: (k4_xboole_0(A_108, k2_xboole_0(B_109, A_108))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2867])).
% 7.71/2.84  tff(c_3285, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_3225])).
% 7.71/2.84  tff(c_26, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.71/2.84  tff(c_2251, plain, (![C_85]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_85)=k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_85)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_2180])).
% 7.71/2.84  tff(c_2287, plain, (![C_85]: (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_85))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_85)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2251])).
% 7.71/2.84  tff(c_4259, plain, (![B_128, A_129]: (k2_xboole_0(B_128, k2_xboole_0(A_129, B_128))=k2_xboole_0(B_128, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1505])).
% 7.71/2.84  tff(c_4321, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2287, c_4259])).
% 7.71/2.84  tff(c_4382, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_4321])).
% 7.71/2.84  tff(c_32, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.71/2.84  tff(c_1315, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1303])).
% 7.71/2.84  tff(c_1792, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1315, c_1754])).
% 7.71/2.84  tff(c_1812, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1792])).
% 7.71/2.84  tff(c_1957, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k4_xboole_0(A_80, B_81), C_82)=k4_xboole_0(A_80, k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.71/2.84  tff(c_5494, plain, (![C_144]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_144))=k4_xboole_0('#skF_6', C_144))), inference(superposition, [status(thm), theory('equality')], [c_1812, c_1957])).
% 7.71/2.84  tff(c_5534, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4382, c_5494])).
% 7.71/2.84  tff(c_5592, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_3', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3285, c_5534])).
% 7.71/2.84  tff(c_6264, plain, (k2_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k2_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5592, c_14])).
% 7.71/2.84  tff(c_6275, plain, (k2_xboole_0('#skF_3', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1552, c_37, c_2200, c_2, c_72, c_2, c_6264])).
% 7.71/2.84  tff(c_1542, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1496])).
% 7.71/2.84  tff(c_7623, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6275, c_1542])).
% 7.71/2.84  tff(c_7645, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_18, c_7623])).
% 7.71/2.84  tff(c_1351, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_1316])).
% 7.71/2.84  tff(c_1783, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1351, c_1754])).
% 7.71/2.84  tff(c_1809, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1783])).
% 7.71/2.84  tff(c_7638, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6275, c_18])).
% 7.71/2.84  tff(c_7650, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1809, c_7638])).
% 7.71/2.84  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.71/2.84  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.71/2.84  tff(c_201, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_24])).
% 7.71/2.84  tff(c_5286, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_201])).
% 7.71/2.84  tff(c_1804, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k3_xboole_0(A_78, B_79))=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_1767])).
% 7.71/2.84  tff(c_5565, plain, (![B_79]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_4', B_79))=k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1804, c_5494])).
% 7.71/2.84  tff(c_6278, plain, (![B_148]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_4', B_148))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_5565])).
% 7.71/2.84  tff(c_6314, plain, (![B_39]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_4', B_39))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5286, c_6278])).
% 7.71/2.84  tff(c_7658, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_7645, c_6314])).
% 7.71/2.84  tff(c_155, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_37])).
% 7.71/2.84  tff(c_1530, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')=k4_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_155, c_1496])).
% 7.71/2.84  tff(c_8079, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7658, c_1530])).
% 7.71/2.84  tff(c_11562, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7650, c_8079])).
% 7.71/2.84  tff(c_11607, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11562, c_1315])).
% 7.71/2.84  tff(c_1394, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1367])).
% 7.71/2.84  tff(c_11920, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11607, c_1394])).
% 7.71/2.84  tff(c_11966, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7645, c_11920])).
% 7.71/2.84  tff(c_11968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_11966])).
% 7.71/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.84  
% 7.71/2.84  Inference rules
% 7.71/2.84  ----------------------
% 7.71/2.84  #Ref     : 0
% 7.71/2.84  #Sup     : 3041
% 7.71/2.84  #Fact    : 0
% 7.71/2.84  #Define  : 0
% 7.71/2.84  #Split   : 1
% 7.71/2.84  #Chain   : 0
% 7.71/2.84  #Close   : 0
% 7.71/2.84  
% 7.71/2.84  Ordering : KBO
% 7.71/2.84  
% 7.71/2.84  Simplification rules
% 7.71/2.84  ----------------------
% 7.71/2.84  #Subsume      : 92
% 7.71/2.84  #Demod        : 2988
% 7.71/2.84  #Tautology    : 2018
% 7.71/2.84  #SimpNegUnit  : 47
% 7.71/2.84  #BackRed      : 63
% 7.71/2.84  
% 7.71/2.84  #Partial instantiations: 0
% 7.71/2.84  #Strategies tried      : 1
% 7.71/2.84  
% 7.71/2.84  Timing (in seconds)
% 7.71/2.84  ----------------------
% 7.71/2.84  Preprocessing        : 0.32
% 7.71/2.84  Parsing              : 0.17
% 7.71/2.84  CNF conversion       : 0.02
% 7.71/2.84  Main loop            : 1.70
% 7.71/2.84  Inferencing          : 0.43
% 7.71/2.84  Reduction            : 0.87
% 7.71/2.84  Demodulation         : 0.74
% 7.71/2.84  BG Simplification    : 0.05
% 7.71/2.84  Subsumption          : 0.23
% 7.71/2.84  Abstraction          : 0.07
% 7.71/2.84  MUC search           : 0.00
% 7.71/2.84  Cooper               : 0.00
% 7.71/2.84  Total                : 2.06
% 7.71/2.85  Index Insertion      : 0.00
% 7.71/2.85  Index Deletion       : 0.00
% 7.71/2.85  Index Matching       : 0.00
% 7.71/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
