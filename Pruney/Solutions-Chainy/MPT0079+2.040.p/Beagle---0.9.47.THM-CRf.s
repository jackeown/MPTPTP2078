%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 268 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :   88 ( 284 expanded)
%              Number of equality atoms :   81 ( 261 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_315,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_342,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_315])).

tff(c_347,plain,(
    ! [A_43] : k4_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_342])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_352,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_xboole_0) = k3_xboole_0(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_20])).

tff(c_364,plain,(
    ! [A_43] : k3_xboole_0(A_43,A_43) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_352])).

tff(c_1528,plain,(
    ! [A_72,B_73,C_74] : k4_xboole_0(k3_xboole_0(A_72,B_73),C_74) = k3_xboole_0(A_72,k4_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1598,plain,(
    ! [A_43,C_74] : k3_xboole_0(A_43,k4_xboole_0(A_43,C_74)) = k4_xboole_0(A_43,C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_1528])).

tff(c_324,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_315])).

tff(c_5786,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_324])).

tff(c_5900,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_5786])).

tff(c_5936,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5900])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_174,plain,(
    ! [A_35,B_36] : k4_xboole_0(k2_xboole_0(A_35,B_36),B_36) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_196,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_345,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_342])).

tff(c_61,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_190,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k4_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_174])).

tff(c_346,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_190])).

tff(c_1004,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1068,plain,(
    ! [A_9,C_62] : k4_xboole_0(A_9,k2_xboole_0(A_9,C_62)) = k4_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1004])).

tff(c_1202,plain,(
    ! [A_65,C_66] : k4_xboole_0(A_65,k2_xboole_0(A_65,C_66)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_1068])).

tff(c_1229,plain,(
    ! [A_65,C_66] : k3_xboole_0(A_65,k2_xboole_0(A_65,C_66)) = k4_xboole_0(A_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_20])).

tff(c_1285,plain,(
    ! [A_65,C_66] : k3_xboole_0(A_65,k2_xboole_0(A_65,C_66)) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1229])).

tff(c_1792,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k4_xboole_0(B_80,k3_xboole_0(A_79,B_80))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1528])).

tff(c_1845,plain,(
    ! [A_65,C_66] : k3_xboole_0(A_65,k4_xboole_0(k2_xboole_0(A_65,C_66),A_65)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_1792])).

tff(c_1899,plain,(
    ! [A_65,C_66] : k3_xboole_0(A_65,k4_xboole_0(C_66,A_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1845])).

tff(c_5981,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5936,c_1899])).

tff(c_5785,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_324])).

tff(c_6401,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5981,c_5785])).

tff(c_6412,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6401])).

tff(c_34,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_424,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_455,plain,(
    ! [B_11,A_10] : k2_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k2_xboole_0(B_11,k2_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_424])).

tff(c_600,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,k2_xboole_0(A_52,B_51)) = k2_xboole_0(B_51,A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_455])).

tff(c_648,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_600])).

tff(c_678,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2,c_648])).

tff(c_834,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_16])).

tff(c_841,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_834])).

tff(c_8940,plain,(
    ! [C_142,A_143,B_144] : k2_xboole_0(C_142,k4_xboole_0(A_143,k2_xboole_0(B_144,C_142))) = k2_xboole_0(C_142,k4_xboole_0(A_143,B_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_12])).

tff(c_9158,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_8940])).

tff(c_9280,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6412,c_8,c_9158])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_5897,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_5786])).

tff(c_5935,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5897])).

tff(c_471,plain,(
    ! [B_11,A_10] : k2_xboole_0(B_11,k2_xboole_0(A_10,B_11)) = k2_xboole_0(B_11,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_455])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_xboole_0(A_20,B_21),C_22) = k2_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_685,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_xboole_0(A_53,B_54),C_55) = k2_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_769,plain,(
    ! [C_55] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_55) = k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_685])).

tff(c_1301,plain,(
    ! [C_67] : k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_67)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_769])).

tff(c_1343,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_1301])).

tff(c_1376,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2,c_1343])).

tff(c_1027,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,k4_xboole_0(A_60,B_61))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_345])).

tff(c_1097,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k2_xboole_0(B_61,A_60)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1027])).

tff(c_2345,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_1097])).

tff(c_9553,plain,(
    ! [A_145] : k2_xboole_0('#skF_2',k4_xboole_0(A_145,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_145,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_8940])).

tff(c_9634,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2345,c_9553])).

tff(c_9707,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9280,c_2,c_5935,c_196,c_8,c_9634])).

tff(c_9709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_9707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.52  
% 7.31/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.52  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.31/2.52  
% 7.31/2.52  %Foreground sorts:
% 7.31/2.52  
% 7.31/2.52  
% 7.31/2.52  %Background operators:
% 7.31/2.52  
% 7.31/2.52  
% 7.31/2.52  %Foreground operators:
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.31/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.52  
% 7.31/2.54  tff(f_60, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 7.31/2.54  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.31/2.54  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.31/2.54  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.31/2.54  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.31/2.54  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.31/2.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.31/2.54  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.31/2.54  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.31/2.54  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.31/2.54  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.31/2.54  tff(f_49, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.31/2.54  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.54  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.54  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.54  tff(c_152, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.54  tff(c_159, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_152])).
% 7.31/2.54  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.54  tff(c_315, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.54  tff(c_342, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_315])).
% 7.31/2.54  tff(c_347, plain, (![A_43]: (k4_xboole_0(A_43, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_342])).
% 7.31/2.54  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.54  tff(c_352, plain, (![A_43]: (k4_xboole_0(A_43, k1_xboole_0)=k3_xboole_0(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_347, c_20])).
% 7.31/2.54  tff(c_364, plain, (![A_43]: (k3_xboole_0(A_43, A_43)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_352])).
% 7.31/2.54  tff(c_1528, plain, (![A_72, B_73, C_74]: (k4_xboole_0(k3_xboole_0(A_72, B_73), C_74)=k3_xboole_0(A_72, k4_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.31/2.54  tff(c_1598, plain, (![A_43, C_74]: (k3_xboole_0(A_43, k4_xboole_0(A_43, C_74))=k4_xboole_0(A_43, C_74))), inference(superposition, [status(thm), theory('equality')], [c_364, c_1528])).
% 7.31/2.54  tff(c_324, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_315])).
% 7.31/2.54  tff(c_5786, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_324])).
% 7.31/2.54  tff(c_5900, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_5786])).
% 7.31/2.54  tff(c_5936, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5900])).
% 7.31/2.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.31/2.54  tff(c_174, plain, (![A_35, B_36]: (k4_xboole_0(k2_xboole_0(A_35, B_36), B_36)=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.54  tff(c_196, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_174])).
% 7.31/2.54  tff(c_345, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_342])).
% 7.31/2.54  tff(c_61, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.31/2.54  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.31/2.54  tff(c_77, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 7.31/2.54  tff(c_190, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k4_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_77, c_174])).
% 7.31/2.54  tff(c_346, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_190])).
% 7.31/2.54  tff(c_1004, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.54  tff(c_1068, plain, (![A_9, C_62]: (k4_xboole_0(A_9, k2_xboole_0(A_9, C_62))=k4_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1004])).
% 7.31/2.54  tff(c_1202, plain, (![A_65, C_66]: (k4_xboole_0(A_65, k2_xboole_0(A_65, C_66))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_1068])).
% 7.31/2.54  tff(c_1229, plain, (![A_65, C_66]: (k3_xboole_0(A_65, k2_xboole_0(A_65, C_66))=k4_xboole_0(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1202, c_20])).
% 7.31/2.54  tff(c_1285, plain, (![A_65, C_66]: (k3_xboole_0(A_65, k2_xboole_0(A_65, C_66))=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1229])).
% 7.31/2.54  tff(c_1792, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k4_xboole_0(B_80, k3_xboole_0(A_79, B_80)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_345, c_1528])).
% 7.31/2.54  tff(c_1845, plain, (![A_65, C_66]: (k3_xboole_0(A_65, k4_xboole_0(k2_xboole_0(A_65, C_66), A_65))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1285, c_1792])).
% 7.31/2.54  tff(c_1899, plain, (![A_65, C_66]: (k3_xboole_0(A_65, k4_xboole_0(C_66, A_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1845])).
% 7.31/2.54  tff(c_5981, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5936, c_1899])).
% 7.31/2.54  tff(c_5785, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_324])).
% 7.31/2.54  tff(c_6401, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5981, c_5785])).
% 7.31/2.54  tff(c_6412, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6401])).
% 7.31/2.54  tff(c_34, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.54  tff(c_35, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 7.31/2.54  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.54  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.54  tff(c_424, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.54  tff(c_455, plain, (![B_11, A_10]: (k2_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k2_xboole_0(B_11, k2_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_424])).
% 7.31/2.54  tff(c_600, plain, (![B_51, A_52]: (k2_xboole_0(B_51, k2_xboole_0(A_52, B_51))=k2_xboole_0(B_51, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_455])).
% 7.31/2.54  tff(c_648, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_600])).
% 7.31/2.54  tff(c_678, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2, c_648])).
% 7.31/2.54  tff(c_834, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_678, c_16])).
% 7.31/2.54  tff(c_841, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_345, c_834])).
% 7.31/2.54  tff(c_8940, plain, (![C_142, A_143, B_144]: (k2_xboole_0(C_142, k4_xboole_0(A_143, k2_xboole_0(B_144, C_142)))=k2_xboole_0(C_142, k4_xboole_0(A_143, B_144)))), inference(superposition, [status(thm), theory('equality')], [c_1004, c_12])).
% 7.31/2.54  tff(c_9158, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_841, c_8940])).
% 7.31/2.54  tff(c_9280, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6412, c_8, c_9158])).
% 7.31/2.54  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.54  tff(c_160, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_152])).
% 7.31/2.54  tff(c_5897, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_160, c_5786])).
% 7.31/2.54  tff(c_5935, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5897])).
% 7.31/2.54  tff(c_471, plain, (![B_11, A_10]: (k2_xboole_0(B_11, k2_xboole_0(A_10, B_11))=k2_xboole_0(B_11, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_455])).
% 7.31/2.54  tff(c_24, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k2_xboole_0(A_20, B_21), C_22)=k2_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.54  tff(c_685, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_xboole_0(A_53, B_54), C_55)=k2_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.54  tff(c_769, plain, (![C_55]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_55)=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_55)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_685])).
% 7.31/2.54  tff(c_1301, plain, (![C_67]: (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_67))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_67)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_769])).
% 7.31/2.54  tff(c_1343, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_471, c_1301])).
% 7.31/2.54  tff(c_1376, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2, c_1343])).
% 7.31/2.54  tff(c_1027, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, k4_xboole_0(A_60, B_61)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1004, c_345])).
% 7.31/2.54  tff(c_1097, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k2_xboole_0(B_61, A_60))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1027])).
% 7.31/2.54  tff(c_2345, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1376, c_1097])).
% 7.31/2.54  tff(c_9553, plain, (![A_145]: (k2_xboole_0('#skF_2', k4_xboole_0(A_145, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_145, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35, c_8940])).
% 7.31/2.54  tff(c_9634, plain, (k2_xboole_0('#skF_2', k4_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2345, c_9553])).
% 7.31/2.54  tff(c_9707, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9280, c_2, c_5935, c_196, c_8, c_9634])).
% 7.31/2.54  tff(c_9709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_9707])).
% 7.31/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.54  
% 7.31/2.54  Inference rules
% 7.31/2.54  ----------------------
% 7.31/2.54  #Ref     : 0
% 7.31/2.54  #Sup     : 2448
% 7.31/2.54  #Fact    : 0
% 7.31/2.54  #Define  : 0
% 7.31/2.54  #Split   : 0
% 7.31/2.54  #Chain   : 0
% 7.31/2.54  #Close   : 0
% 7.31/2.54  
% 7.31/2.54  Ordering : KBO
% 7.31/2.54  
% 7.31/2.54  Simplification rules
% 7.31/2.54  ----------------------
% 7.31/2.54  #Subsume      : 59
% 7.31/2.54  #Demod        : 2773
% 7.31/2.54  #Tautology    : 1578
% 7.31/2.54  #SimpNegUnit  : 1
% 7.31/2.54  #BackRed      : 3
% 7.31/2.54  
% 7.31/2.54  #Partial instantiations: 0
% 7.31/2.54  #Strategies tried      : 1
% 7.31/2.54  
% 7.31/2.54  Timing (in seconds)
% 7.31/2.54  ----------------------
% 7.31/2.54  Preprocessing        : 0.30
% 7.31/2.54  Parsing              : 0.16
% 7.31/2.54  CNF conversion       : 0.02
% 7.31/2.54  Main loop            : 1.47
% 7.31/2.54  Inferencing          : 0.35
% 7.31/2.54  Reduction            : 0.83
% 7.31/2.54  Demodulation         : 0.73
% 7.31/2.54  BG Simplification    : 0.04
% 7.31/2.54  Subsumption          : 0.18
% 7.31/2.54  Abstraction          : 0.06
% 7.31/2.54  MUC search           : 0.00
% 7.31/2.54  Cooper               : 0.00
% 7.31/2.54  Total                : 1.80
% 7.31/2.54  Index Insertion      : 0.00
% 7.31/2.54  Index Deletion       : 0.00
% 7.31/2.54  Index Matching       : 0.00
% 7.31/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
