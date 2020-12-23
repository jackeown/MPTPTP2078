%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 662 expanded)
%              Number of leaves         :   28 ( 241 expanded)
%              Depth                    :   22
%              Number of atoms          :  112 ( 783 expanded)
%              Number of equality atoms :   92 ( 636 expanded)
%              Maximal formula depth    :    9 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_28,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1372,plain,(
    ! [A_69,B_70] :
      ( ~ r1_xboole_0(A_69,B_70)
      | k3_xboole_0(A_69,B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_1390,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_1372])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1397,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_20])).

tff(c_1403,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1397])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1579,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1623,plain,(
    ! [B_16,A_15] : k2_xboole_0(B_16,k4_xboole_0(A_15,B_16)) = k2_xboole_0(B_16,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1579])).

tff(c_1645,plain,(
    ! [B_16,A_15] : k2_xboole_0(B_16,k2_xboole_0(A_15,B_16)) = k2_xboole_0(B_16,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1623])).

tff(c_34,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_49,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_49])).

tff(c_2085,plain,(
    ! [A_80,B_81,C_82] : k2_xboole_0(k2_xboole_0(A_80,B_81),C_82) = k2_xboole_0(A_80,k2_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2160,plain,(
    ! [A_80,B_81,A_1] : k2_xboole_0(A_80,k2_xboole_0(B_81,A_1)) = k2_xboole_0(A_1,k2_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2085])).

tff(c_169,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_14])).

tff(c_200,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_179])).

tff(c_203,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_179])).

tff(c_212,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_117,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_132,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_231,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_241,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k4_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_16])).

tff(c_265,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k3_xboole_0(A_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_241])).

tff(c_26,plain,(
    ! [A_27,B_28] : k2_xboole_0(k3_xboole_0(A_27,B_28),k4_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1616,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = k2_xboole_0(k3_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1579])).

tff(c_2373,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_1616])).

tff(c_2478,plain,(
    ! [B_86] : k3_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2373,c_212])).

tff(c_2493,plain,(
    ! [B_86] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_86)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2478,c_26])).

tff(c_2506,plain,(
    ! [B_86] : k3_xboole_0(B_86,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_265,c_2493])).

tff(c_2696,plain,(
    ! [A_92] : k4_xboole_0(A_92,A_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_132])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k4_xboole_0(A_17,B_18),C_19) = k4_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2708,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(B_18,k4_xboole_0(A_17,B_18))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2696,c_18])).

tff(c_3221,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k2_xboole_0(B_104,A_103)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2708])).

tff(c_3296,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_3221])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_xboole_0(A_24,B_25),C_26) = k2_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2163,plain,(
    ! [C_82] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_82) = k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_2085])).

tff(c_2176,plain,(
    ! [C_82] : k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_82)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2163])).

tff(c_3430,plain,(
    ! [B_109,A_110] : k2_xboole_0(B_109,k2_xboole_0(A_110,B_109)) = k2_xboole_0(B_109,A_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1623])).

tff(c_3489,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2176,c_3430])).

tff(c_3543,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2,c_3489])).

tff(c_30,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1392,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1372])).

tff(c_1423,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1392,c_20])).

tff(c_1429,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1423])).

tff(c_1876,plain,(
    ! [A_77,B_78,C_79] : k4_xboole_0(k4_xboole_0(A_77,B_78),C_79) = k4_xboole_0(A_77,k2_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6624,plain,(
    ! [C_139] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_139)) = k4_xboole_0('#skF_6',C_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_1876])).

tff(c_6673,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3543,c_6624])).

tff(c_6736,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_6673])).

tff(c_7114,plain,(
    k2_xboole_0(k2_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k2_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6736,c_12])).

tff(c_7129,plain,(
    k2_xboole_0('#skF_3','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1645,c_85,c_2,c_2160,c_2,c_200,c_7114])).

tff(c_7977,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7129,c_16])).

tff(c_7993,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_7977])).

tff(c_1393,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1372])).

tff(c_1486,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_20])).

tff(c_1492,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1486])).

tff(c_188,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_7971,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_3') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7129,c_188])).

tff(c_7991,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_16,c_7971])).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_5699,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_126])).

tff(c_1643,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_1616])).

tff(c_6708,plain,(
    ! [B_21] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_4',B_21)) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1643,c_6624])).

tff(c_7013,plain,(
    ! [B_141] : k4_xboole_0('#skF_6',k3_xboole_0('#skF_4',B_141)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_6708])).

tff(c_7051,plain,(
    ! [B_23] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_4',B_23)) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_7013])).

tff(c_7999,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7991,c_7051])).

tff(c_185,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_169])).

tff(c_8502,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7999,c_185])).

tff(c_11021,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7993,c_8502])).

tff(c_99,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_1391,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_1372])).

tff(c_1410,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_20])).

tff(c_1416,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1410])).

tff(c_11056,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11021,c_1416])).

tff(c_11100,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11056,c_7991])).

tff(c_11102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_11100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:56:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.86/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.71  
% 7.86/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/2.71  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.86/2.71  
% 7.86/2.71  %Foreground sorts:
% 7.86/2.71  
% 7.86/2.71  
% 7.86/2.71  %Background operators:
% 7.86/2.71  
% 7.86/2.71  
% 7.86/2.71  %Foreground operators:
% 7.86/2.71  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.86/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.86/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.86/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.86/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.86/2.71  tff('#skF_5', type, '#skF_5': $i).
% 7.86/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.86/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.86/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.86/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.86/2.71  tff('#skF_4', type, '#skF_4': $i).
% 7.86/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.86/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.86/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.86/2.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.86/2.71  
% 8.01/2.73  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.01/2.73  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.01/2.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.01/2.73  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.01/2.73  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.01/2.73  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.01/2.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.01/2.73  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.01/2.73  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.01/2.73  tff(f_67, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.01/2.73  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.01/2.73  tff(f_69, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.01/2.73  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.01/2.73  tff(c_28, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.01/2.73  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.01/2.73  tff(c_32, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.01/2.73  tff(c_94, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.73  tff(c_100, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_94])).
% 8.01/2.73  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.01/2.73  tff(c_135, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.01/2.73  tff(c_1372, plain, (![A_69, B_70]: (~r1_xboole_0(A_69, B_70) | k3_xboole_0(A_69, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_135])).
% 8.01/2.73  tff(c_1390, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_1372])).
% 8.01/2.73  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.01/2.73  tff(c_1397, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1390, c_20])).
% 8.01/2.73  tff(c_1403, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1397])).
% 8.01/2.73  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.01/2.73  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.01/2.73  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.01/2.73  tff(c_1579, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.01/2.73  tff(c_1623, plain, (![B_16, A_15]: (k2_xboole_0(B_16, k4_xboole_0(A_15, B_16))=k2_xboole_0(B_16, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1579])).
% 8.01/2.73  tff(c_1645, plain, (![B_16, A_15]: (k2_xboole_0(B_16, k2_xboole_0(A_15, B_16))=k2_xboole_0(B_16, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1623])).
% 8.01/2.73  tff(c_34, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.01/2.73  tff(c_35, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 8.01/2.73  tff(c_49, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.01/2.73  tff(c_85, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35, c_49])).
% 8.01/2.73  tff(c_2085, plain, (![A_80, B_81, C_82]: (k2_xboole_0(k2_xboole_0(A_80, B_81), C_82)=k2_xboole_0(A_80, k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.01/2.73  tff(c_2160, plain, (![A_80, B_81, A_1]: (k2_xboole_0(A_80, k2_xboole_0(B_81, A_1))=k2_xboole_0(A_1, k2_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2085])).
% 8.01/2.73  tff(c_169, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.01/2.73  tff(c_179, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_14])).
% 8.01/2.73  tff(c_200, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_179])).
% 8.01/2.73  tff(c_203, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_179])).
% 8.01/2.73  tff(c_212, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 8.01/2.73  tff(c_117, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.01/2.73  tff(c_132, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_117])).
% 8.01/2.73  tff(c_231, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 8.01/2.73  tff(c_241, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k4_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_231, c_16])).
% 8.01/2.73  tff(c_265, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k3_xboole_0(A_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_241])).
% 8.01/2.73  tff(c_26, plain, (![A_27, B_28]: (k2_xboole_0(k3_xboole_0(A_27, B_28), k4_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.01/2.73  tff(c_1616, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=k2_xboole_0(k3_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1579])).
% 8.01/2.73  tff(c_2373, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k3_xboole_0(A_84, B_85))=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_1616])).
% 8.01/2.73  tff(c_2478, plain, (![B_86]: (k3_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2373, c_212])).
% 8.01/2.73  tff(c_2493, plain, (![B_86]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_86))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2478, c_26])).
% 8.01/2.73  tff(c_2506, plain, (![B_86]: (k3_xboole_0(B_86, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_265, c_2493])).
% 8.01/2.73  tff(c_2696, plain, (![A_92]: (k4_xboole_0(A_92, A_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2506, c_132])).
% 8.01/2.73  tff(c_18, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k4_xboole_0(A_17, B_18), C_19)=k4_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.01/2.73  tff(c_2708, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(B_18, k4_xboole_0(A_17, B_18)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2696, c_18])).
% 8.01/2.73  tff(c_3221, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k2_xboole_0(B_104, A_103))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2708])).
% 8.01/2.73  tff(c_3296, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35, c_3221])).
% 8.01/2.73  tff(c_24, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_xboole_0(A_24, B_25), C_26)=k2_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.01/2.73  tff(c_2163, plain, (![C_82]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_82)=k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_82)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_2085])).
% 8.01/2.73  tff(c_2176, plain, (![C_82]: (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_82))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_82)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2163])).
% 8.01/2.73  tff(c_3430, plain, (![B_109, A_110]: (k2_xboole_0(B_109, k2_xboole_0(A_110, B_109))=k2_xboole_0(B_109, A_110))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1623])).
% 8.01/2.73  tff(c_3489, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2176, c_3430])).
% 8.01/2.73  tff(c_3543, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2, c_3489])).
% 8.01/2.73  tff(c_30, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.01/2.73  tff(c_1392, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_1372])).
% 8.01/2.73  tff(c_1423, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1392, c_20])).
% 8.01/2.73  tff(c_1429, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1423])).
% 8.01/2.73  tff(c_1876, plain, (![A_77, B_78, C_79]: (k4_xboole_0(k4_xboole_0(A_77, B_78), C_79)=k4_xboole_0(A_77, k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.01/2.73  tff(c_6624, plain, (![C_139]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_139))=k4_xboole_0('#skF_6', C_139))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_1876])).
% 8.01/2.73  tff(c_6673, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3543, c_6624])).
% 8.01/2.73  tff(c_6736, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_3', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_6673])).
% 8.01/2.73  tff(c_7114, plain, (k2_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k2_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6736, c_12])).
% 8.01/2.73  tff(c_7129, plain, (k2_xboole_0('#skF_3', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1645, c_85, c_2, c_2160, c_2, c_200, c_7114])).
% 8.01/2.73  tff(c_7977, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7129, c_16])).
% 8.01/2.73  tff(c_7993, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_7977])).
% 8.01/2.73  tff(c_1393, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1372])).
% 8.01/2.73  tff(c_1486, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1393, c_20])).
% 8.01/2.73  tff(c_1492, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1486])).
% 8.01/2.73  tff(c_188, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_169])).
% 8.01/2.73  tff(c_7971, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7129, c_188])).
% 8.01/2.73  tff(c_7991, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_16, c_7971])).
% 8.01/2.73  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.01/2.73  tff(c_126, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k3_xboole_0(A_22, k4_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 8.01/2.73  tff(c_5699, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_126])).
% 8.01/2.73  tff(c_1643, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k3_xboole_0(A_20, B_21))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_1616])).
% 8.01/2.73  tff(c_6708, plain, (![B_21]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_4', B_21))=k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1643, c_6624])).
% 8.01/2.73  tff(c_7013, plain, (![B_141]: (k4_xboole_0('#skF_6', k3_xboole_0('#skF_4', B_141))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1429, c_6708])).
% 8.01/2.73  tff(c_7051, plain, (![B_23]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_4', B_23))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5699, c_7013])).
% 8.01/2.73  tff(c_7999, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_7991, c_7051])).
% 8.01/2.73  tff(c_185, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')=k4_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_85, c_169])).
% 8.01/2.73  tff(c_8502, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7999, c_185])).
% 8.01/2.73  tff(c_11021, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7993, c_8502])).
% 8.01/2.73  tff(c_99, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_30, c_94])).
% 8.01/2.73  tff(c_1391, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_1372])).
% 8.01/2.73  tff(c_1410, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1391, c_20])).
% 8.01/2.73  tff(c_1416, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1410])).
% 8.01/2.73  tff(c_11056, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11021, c_1416])).
% 8.01/2.73  tff(c_11100, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11056, c_7991])).
% 8.01/2.73  tff(c_11102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_11100])).
% 8.01/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.73  
% 8.01/2.73  Inference rules
% 8.01/2.73  ----------------------
% 8.01/2.73  #Ref     : 0
% 8.01/2.73  #Sup     : 2830
% 8.01/2.73  #Fact    : 0
% 8.01/2.73  #Define  : 0
% 8.01/2.73  #Split   : 2
% 8.01/2.73  #Chain   : 0
% 8.01/2.73  #Close   : 0
% 8.01/2.73  
% 8.01/2.73  Ordering : KBO
% 8.01/2.73  
% 8.01/2.73  Simplification rules
% 8.01/2.73  ----------------------
% 8.01/2.73  #Subsume      : 70
% 8.01/2.73  #Demod        : 2983
% 8.01/2.73  #Tautology    : 1735
% 8.01/2.73  #SimpNegUnit  : 29
% 8.01/2.73  #BackRed      : 57
% 8.01/2.73  
% 8.01/2.73  #Partial instantiations: 0
% 8.01/2.73  #Strategies tried      : 1
% 8.01/2.73  
% 8.01/2.73  Timing (in seconds)
% 8.01/2.73  ----------------------
% 8.01/2.74  Preprocessing        : 0.30
% 8.01/2.74  Parsing              : 0.17
% 8.01/2.74  CNF conversion       : 0.02
% 8.01/2.74  Main loop            : 1.64
% 8.01/2.74  Inferencing          : 0.40
% 8.01/2.74  Reduction            : 0.88
% 8.01/2.74  Demodulation         : 0.76
% 8.01/2.74  BG Simplification    : 0.05
% 8.01/2.74  Subsumption          : 0.21
% 8.01/2.74  Abstraction          : 0.07
% 8.01/2.74  MUC search           : 0.00
% 8.01/2.74  Cooper               : 0.00
% 8.01/2.74  Total                : 1.99
% 8.01/2.74  Index Insertion      : 0.00
% 8.01/2.74  Index Deletion       : 0.00
% 8.01/2.74  Index Matching       : 0.00
% 8.01/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
