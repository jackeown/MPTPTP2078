%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  127 (4142 expanded)
%              Number of leaves         :   27 (1448 expanded)
%              Depth                    :   25
%              Number of atoms          :  118 (4137 expanded)
%              Number of equality atoms :  107 (4122 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [C_28,A_26,B_27] :
      ( k4_xboole_0(C_28,k2_tarski(A_26,B_27)) = C_28
      | r2_hidden(B_27,C_28)
      | r2_hidden(A_26,C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_284,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_299,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_284])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_305,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_284])).

tff(c_49,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_8,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_35] : k3_xboole_0(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_65,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_524,plain,(
    ! [A_60,B_61,C_62] : k5_xboole_0(k5_xboole_0(A_60,B_61),C_62) = k5_xboole_0(A_60,k5_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_541,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k5_xboole_0(B_61,k2_xboole_0(A_60,B_61))) = k3_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_14])).

tff(c_1188,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k5_xboole_0(B_78,k2_xboole_0(A_77,B_78))) = k3_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_14])).

tff(c_1231,plain,(
    ! [A_5] : k5_xboole_0(A_5,k5_xboole_0(k1_xboole_0,A_5)) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1188])).

tff(c_1238,plain,(
    ! [A_79] : k5_xboole_0(A_79,k5_xboole_0(k1_xboole_0,A_79)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1231])).

tff(c_1268,plain,(
    ! [B_61] : k5_xboole_0(k5_xboole_0(B_61,k2_xboole_0(k1_xboole_0,B_61)),k3_xboole_0(k1_xboole_0,B_61)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_1238])).

tff(c_1312,plain,(
    ! [B_61] : k4_xboole_0(k4_xboole_0(B_61,B_61),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_305,c_120,c_65,c_1268])).

tff(c_846,plain,(
    ! [A_70,B_71,C_72] : k2_xboole_0(k4_xboole_0(A_70,k2_xboole_0(B_71,C_72)),k4_xboole_0(B_71,k2_xboole_0(A_70,C_72))) = k4_xboole_0(k5_xboole_0(A_70,B_71),C_72) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_930,plain,(
    ! [A_70,A_5] : k2_xboole_0(k4_xboole_0(A_70,A_5),k4_xboole_0(A_5,k2_xboole_0(A_70,k1_xboole_0))) = k4_xboole_0(k5_xboole_0(A_70,A_5),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_846])).

tff(c_3050,plain,(
    ! [A_106,A_107] : k2_xboole_0(k4_xboole_0(A_106,A_107),k4_xboole_0(A_107,A_106)) = k4_xboole_0(k5_xboole_0(A_106,A_107),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_930])).

tff(c_345,plain,(
    ! [A_53] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_284])).

tff(c_296,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_284])).

tff(c_370,plain,(
    ! [A_55,A_54] : k4_xboole_0(k1_xboole_0,A_55) = k4_xboole_0(k1_xboole_0,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_296])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    ! [A_55,A_54] : k5_xboole_0(A_55,k4_xboole_0(k1_xboole_0,A_54)) = k2_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_16])).

tff(c_402,plain,(
    ! [A_55,A_54] : k5_xboole_0(A_55,k4_xboole_0(k1_xboole_0,A_54)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_388])).

tff(c_1321,plain,(
    ! [B_80] : k4_xboole_0(k4_xboole_0(B_80,B_80),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_305,c_120,c_65,c_1268])).

tff(c_1335,plain,(
    ! [B_80] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_80,B_80)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_16])).

tff(c_1798,plain,(
    ! [B_89] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_89,B_89)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_1335])).

tff(c_1854,plain,(
    ! [B_90] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(B_90,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1798,c_65])).

tff(c_1910,plain,(
    ! [B_90] : k5_xboole_0(B_90,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(B_90,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_16])).

tff(c_1940,plain,(
    ! [B_90] : k2_xboole_0(B_90,B_90) = B_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_1910])).

tff(c_3057,plain,(
    ! [A_107] : k4_xboole_0(k5_xboole_0(A_107,A_107),k1_xboole_0) = k4_xboole_0(A_107,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_3050,c_1940])).

tff(c_3183,plain,(
    ! [A_107] : k4_xboole_0(A_107,A_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_299,c_3057])).

tff(c_1869,plain,(
    ! [A_55,B_90] : k5_xboole_0(A_55,k4_xboole_0(B_90,B_90)) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_402])).

tff(c_3209,plain,(
    ! [A_55] : k5_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_1869])).

tff(c_403,plain,(
    ! [A_56,B_57] : k5_xboole_0(k5_xboole_0(A_56,B_57),k2_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_421,plain,(
    ! [A_5] : k5_xboole_0(k4_xboole_0(A_5,A_5),k2_xboole_0(A_5,A_5)) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_403])).

tff(c_448,plain,(
    ! [A_5] : k5_xboole_0(k4_xboole_0(A_5,A_5),k2_xboole_0(A_5,A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_421])).

tff(c_1942,plain,(
    ! [A_5] : k5_xboole_0(k4_xboole_0(A_5,A_5),A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1940,c_448])).

tff(c_3207,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_1942])).

tff(c_4725,plain,(
    ! [A_137,B_138,C_139] : k5_xboole_0(k5_xboole_0(A_137,B_138),k5_xboole_0(k2_xboole_0(A_137,B_138),C_139)) = k5_xboole_0(k3_xboole_0(A_137,B_138),C_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_524])).

tff(c_4916,plain,(
    ! [A_32,C_139] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_32),k5_xboole_0(A_32,C_139)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,A_32),C_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4725])).

tff(c_4961,plain,(
    ! [A_32,C_139] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_139)) = C_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_3207,c_120,c_4916])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_293,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_284])).

tff(c_1410,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_293])).

tff(c_3212,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_1410])).

tff(c_6242,plain,(
    ! [B_157,A_158,C_159] : k2_xboole_0(k4_xboole_0(B_157,k2_xboole_0(A_158,C_159)),k4_xboole_0(A_158,k2_xboole_0(B_157,C_159))) = k4_xboole_0(k5_xboole_0(A_158,B_157),C_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_2])).

tff(c_6366,plain,(
    ! [B_157,B_90] : k2_xboole_0(k4_xboole_0(B_157,B_90),k4_xboole_0(B_90,k2_xboole_0(B_157,B_90))) = k4_xboole_0(k5_xboole_0(B_90,B_157),B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_6242])).

tff(c_6426,plain,(
    ! [B_90,B_157] : k4_xboole_0(k5_xboole_0(B_90,B_157),B_90) = k4_xboole_0(B_157,B_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3212,c_6366])).

tff(c_433,plain,(
    ! [A_32] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_32),A_32) = k3_xboole_0(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_403])).

tff(c_480,plain,(
    ! [A_59] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_59),A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_433])).

tff(c_514,plain,(
    ! [B_15] : k5_xboole_0(k2_xboole_0(k1_xboole_0,B_15),k4_xboole_0(B_15,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_480])).

tff(c_523,plain,(
    ! [B_15] : k5_xboole_0(B_15,k4_xboole_0(B_15,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_514])).

tff(c_442,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,k1_xboole_0),A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_403])).

tff(c_451,plain,(
    ! [A_5] : k5_xboole_0(k4_xboole_0(A_5,k1_xboole_0),A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_10,c_442])).

tff(c_2696,plain,(
    ! [A_102,C_103] : k5_xboole_0(k4_xboole_0(A_102,k1_xboole_0),k5_xboole_0(A_102,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_524])).

tff(c_2782,plain,(
    ! [B_15] : k5_xboole_0(k4_xboole_0(B_15,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_15,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_2696])).

tff(c_2839,plain,(
    ! [B_104] : k4_xboole_0(k4_xboole_0(B_104,k1_xboole_0),k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_65,c_16,c_2782])).

tff(c_2865,plain,(
    ! [B_104] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_104,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_2839,c_16])).

tff(c_2916,plain,(
    ! [B_104] : k5_xboole_0(k1_xboole_0,B_104) = k4_xboole_0(B_104,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2865])).

tff(c_3291,plain,(
    ! [B_104] : k4_xboole_0(B_104,k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_2916])).

tff(c_933,plain,(
    ! [A_5,B_71] : k2_xboole_0(k4_xboole_0(A_5,k2_xboole_0(B_71,k1_xboole_0)),k4_xboole_0(B_71,A_5)) = k4_xboole_0(k5_xboole_0(A_5,B_71),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_846])).

tff(c_945,plain,(
    ! [A_5,B_71] : k2_xboole_0(k4_xboole_0(A_5,B_71),k4_xboole_0(B_71,A_5)) = k4_xboole_0(k5_xboole_0(A_5,B_71),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_933])).

tff(c_3965,plain,(
    ! [A_5,B_71] : k2_xboole_0(k4_xboole_0(A_5,B_71),k4_xboole_0(B_71,A_5)) = k5_xboole_0(A_5,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_945])).

tff(c_4566,plain,(
    ! [A_133,B_134] : k4_xboole_0(A_133,k2_xboole_0(B_134,A_133)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_1410])).

tff(c_9151,plain,(
    ! [B_195,A_196] : k4_xboole_0(k4_xboole_0(B_195,A_196),k5_xboole_0(A_196,B_195)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3965,c_4566])).

tff(c_9206,plain,(
    ! [B_157,B_90] : k4_xboole_0(k4_xboole_0(B_157,B_90),k5_xboole_0(B_90,k5_xboole_0(B_90,B_157))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6426,c_9151])).

tff(c_9335,plain,(
    ! [B_197,B_198] : k4_xboole_0(k4_xboole_0(B_197,B_198),B_197) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4961,c_9206])).

tff(c_9424,plain,(
    ! [B_197,B_198] : k2_xboole_0(B_197,k4_xboole_0(B_197,B_198)) = k5_xboole_0(B_197,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9335,c_16])).

tff(c_9486,plain,(
    ! [B_197,B_198] : k2_xboole_0(B_197,k4_xboole_0(B_197,B_198)) = B_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_9424])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3484,plain,(
    ! [A_112] : k5_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_299])).

tff(c_3529,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k5_xboole_0(B_10,k5_xboole_0(A_9,B_10))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3484])).

tff(c_4964,plain,(
    ! [A_140,C_141] : k5_xboole_0(A_140,k5_xboole_0(A_140,C_141)) = C_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_3207,c_120,c_4916])).

tff(c_5067,plain,(
    ! [B_10,A_9] : k5_xboole_0(B_10,k5_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3529,c_4964])).

tff(c_5275,plain,(
    ! [B_144,A_145] : k5_xboole_0(B_144,k5_xboole_0(A_145,B_144)) = A_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_5067])).

tff(c_5284,plain,(
    ! [B_144,A_145] : k5_xboole_0(B_144,A_145) = k5_xboole_0(A_145,B_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_5275,c_4961])).

tff(c_4615,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4566])).

tff(c_5123,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k4_xboole_0(B_15,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4964])).

tff(c_5950,plain,(
    ! [A_152,A_153,B_154] : k2_xboole_0(k4_xboole_0(A_152,k2_xboole_0(A_153,B_154)),k4_xboole_0(B_154,k2_xboole_0(A_152,A_153))) = k4_xboole_0(k5_xboole_0(A_152,B_154),A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_846])).

tff(c_6055,plain,(
    ! [A_152,B_90] : k2_xboole_0(k4_xboole_0(A_152,B_90),k4_xboole_0(B_90,k2_xboole_0(A_152,B_90))) = k4_xboole_0(k5_xboole_0(A_152,B_90),B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_5950])).

tff(c_7023,plain,(
    ! [A_167,B_168] : k4_xboole_0(k5_xboole_0(A_167,B_168),B_168) = k4_xboole_0(A_167,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3212,c_6055])).

tff(c_7101,plain,(
    ! [B_15,A_14] : k4_xboole_0(k4_xboole_0(B_15,A_14),k2_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_7023])).

tff(c_12285,plain,(
    ! [B_231,A_232] : k4_xboole_0(k4_xboole_0(B_231,A_232),k2_xboole_0(A_232,B_231)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4615,c_7101])).

tff(c_870,plain,(
    ! [B_71,A_70,C_72] : k2_xboole_0(k4_xboole_0(B_71,k2_xboole_0(A_70,C_72)),k4_xboole_0(A_70,k2_xboole_0(B_71,C_72))) = k4_xboole_0(k5_xboole_0(A_70,B_71),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_2])).

tff(c_12341,plain,(
    ! [A_232,B_231] : k2_xboole_0(k4_xboole_0(A_232,k2_xboole_0(k4_xboole_0(B_231,A_232),B_231)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(k4_xboole_0(B_231,A_232),A_232),B_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_12285,c_870])).

tff(c_12494,plain,(
    ! [A_232,B_231] : k4_xboole_0(k2_xboole_0(A_232,B_231),B_231) = k4_xboole_0(A_232,B_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9486,c_16,c_5284,c_2,c_6,c_12341])).

tff(c_28,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14675,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12494,c_28])).

tff(c_14916,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14675])).

tff(c_14920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_14916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.29  
% 8.09/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.09/3.29  
% 8.09/3.29  %Foreground sorts:
% 8.09/3.29  
% 8.09/3.29  
% 8.09/3.29  %Background operators:
% 8.09/3.29  
% 8.09/3.29  
% 8.09/3.29  %Foreground operators:
% 8.09/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.09/3.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.09/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.09/3.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.09/3.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.09/3.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.09/3.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.09/3.29  tff('#skF_2', type, '#skF_2': $i).
% 8.09/3.29  tff('#skF_3', type, '#skF_3': $i).
% 8.09/3.29  tff('#skF_1', type, '#skF_1': $i).
% 8.09/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/3.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.09/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/3.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/3.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.09/3.29  
% 8.09/3.32  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 8.09/3.32  tff(f_59, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 8.09/3.32  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.09/3.32  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 8.09/3.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.09/3.32  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.09/3.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.09/3.32  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.09/3.32  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.09/3.32  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 8.09/3.32  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.09/3.32  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.09/3.32  tff(c_30, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.09/3.32  tff(c_26, plain, (![C_28, A_26, B_27]: (k4_xboole_0(C_28, k2_tarski(A_26, B_27))=C_28 | r2_hidden(B_27, C_28) | r2_hidden(A_26, C_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.09/3.32  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/3.32  tff(c_96, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.09/3.32  tff(c_111, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 8.09/3.32  tff(c_284, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.09/3.32  tff(c_299, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_111, c_284])).
% 8.09/3.32  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.09/3.32  tff(c_305, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_284])).
% 8.09/3.32  tff(c_49, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/3.32  tff(c_114, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 8.09/3.32  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k2_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.09/3.32  tff(c_120, plain, (![A_35]: (k3_xboole_0(k1_xboole_0, A_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 8.09/3.32  tff(c_65, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 8.09/3.32  tff(c_524, plain, (![A_60, B_61, C_62]: (k5_xboole_0(k5_xboole_0(A_60, B_61), C_62)=k5_xboole_0(A_60, k5_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/3.32  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/3.32  tff(c_541, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k5_xboole_0(B_61, k2_xboole_0(A_60, B_61)))=k3_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_524, c_14])).
% 8.09/3.32  tff(c_1188, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k5_xboole_0(B_78, k2_xboole_0(A_77, B_78)))=k3_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_524, c_14])).
% 8.09/3.32  tff(c_1231, plain, (![A_5]: (k5_xboole_0(A_5, k5_xboole_0(k1_xboole_0, A_5))=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1188])).
% 8.09/3.32  tff(c_1238, plain, (![A_79]: (k5_xboole_0(A_79, k5_xboole_0(k1_xboole_0, A_79))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1231])).
% 8.09/3.32  tff(c_1268, plain, (![B_61]: (k5_xboole_0(k5_xboole_0(B_61, k2_xboole_0(k1_xboole_0, B_61)), k3_xboole_0(k1_xboole_0, B_61))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_541, c_1238])).
% 8.09/3.32  tff(c_1312, plain, (![B_61]: (k4_xboole_0(k4_xboole_0(B_61, B_61), k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_299, c_305, c_120, c_65, c_1268])).
% 8.09/3.32  tff(c_846, plain, (![A_70, B_71, C_72]: (k2_xboole_0(k4_xboole_0(A_70, k2_xboole_0(B_71, C_72)), k4_xboole_0(B_71, k2_xboole_0(A_70, C_72)))=k4_xboole_0(k5_xboole_0(A_70, B_71), C_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.09/3.32  tff(c_930, plain, (![A_70, A_5]: (k2_xboole_0(k4_xboole_0(A_70, A_5), k4_xboole_0(A_5, k2_xboole_0(A_70, k1_xboole_0)))=k4_xboole_0(k5_xboole_0(A_70, A_5), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_846])).
% 8.09/3.32  tff(c_3050, plain, (![A_106, A_107]: (k2_xboole_0(k4_xboole_0(A_106, A_107), k4_xboole_0(A_107, A_106))=k4_xboole_0(k5_xboole_0(A_106, A_107), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_930])).
% 8.09/3.32  tff(c_345, plain, (![A_53]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_53))), inference(superposition, [status(thm), theory('equality')], [c_120, c_284])).
% 8.09/3.32  tff(c_296, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_35))), inference(superposition, [status(thm), theory('equality')], [c_120, c_284])).
% 8.09/3.32  tff(c_370, plain, (![A_55, A_54]: (k4_xboole_0(k1_xboole_0, A_55)=k4_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_345, c_296])).
% 8.09/3.32  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.09/3.32  tff(c_388, plain, (![A_55, A_54]: (k5_xboole_0(A_55, k4_xboole_0(k1_xboole_0, A_54))=k2_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_370, c_16])).
% 8.09/3.32  tff(c_402, plain, (![A_55, A_54]: (k5_xboole_0(A_55, k4_xboole_0(k1_xboole_0, A_54))=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_388])).
% 8.09/3.32  tff(c_1321, plain, (![B_80]: (k4_xboole_0(k4_xboole_0(B_80, B_80), k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_299, c_305, c_120, c_65, c_1268])).
% 8.09/3.32  tff(c_1335, plain, (![B_80]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_80, B_80))=k5_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_16])).
% 8.09/3.32  tff(c_1798, plain, (![B_89]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_89, B_89))=k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_1335])).
% 8.09/3.32  tff(c_1854, plain, (![B_90]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(B_90, B_90))), inference(superposition, [status(thm), theory('equality')], [c_1798, c_65])).
% 8.09/3.32  tff(c_1910, plain, (![B_90]: (k5_xboole_0(B_90, k4_xboole_0(k1_xboole_0, k1_xboole_0))=k2_xboole_0(B_90, B_90))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_16])).
% 8.09/3.32  tff(c_1940, plain, (![B_90]: (k2_xboole_0(B_90, B_90)=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_1910])).
% 8.09/3.32  tff(c_3057, plain, (![A_107]: (k4_xboole_0(k5_xboole_0(A_107, A_107), k1_xboole_0)=k4_xboole_0(A_107, A_107))), inference(superposition, [status(thm), theory('equality')], [c_3050, c_1940])).
% 8.09/3.32  tff(c_3183, plain, (![A_107]: (k4_xboole_0(A_107, A_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_299, c_3057])).
% 8.09/3.32  tff(c_1869, plain, (![A_55, B_90]: (k5_xboole_0(A_55, k4_xboole_0(B_90, B_90))=A_55)), inference(superposition, [status(thm), theory('equality')], [c_1854, c_402])).
% 8.09/3.32  tff(c_3209, plain, (![A_55]: (k5_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_1869])).
% 8.09/3.32  tff(c_403, plain, (![A_56, B_57]: (k5_xboole_0(k5_xboole_0(A_56, B_57), k2_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/3.32  tff(c_421, plain, (![A_5]: (k5_xboole_0(k4_xboole_0(A_5, A_5), k2_xboole_0(A_5, A_5))=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_299, c_403])).
% 8.09/3.32  tff(c_448, plain, (![A_5]: (k5_xboole_0(k4_xboole_0(A_5, A_5), k2_xboole_0(A_5, A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_421])).
% 8.09/3.32  tff(c_1942, plain, (![A_5]: (k5_xboole_0(k4_xboole_0(A_5, A_5), A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_1940, c_448])).
% 8.09/3.32  tff(c_3207, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_1942])).
% 8.09/3.32  tff(c_4725, plain, (![A_137, B_138, C_139]: (k5_xboole_0(k5_xboole_0(A_137, B_138), k5_xboole_0(k2_xboole_0(A_137, B_138), C_139))=k5_xboole_0(k3_xboole_0(A_137, B_138), C_139))), inference(superposition, [status(thm), theory('equality')], [c_14, c_524])).
% 8.09/3.32  tff(c_4916, plain, (![A_32, C_139]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_32), k5_xboole_0(A_32, C_139))=k5_xboole_0(k3_xboole_0(k1_xboole_0, A_32), C_139))), inference(superposition, [status(thm), theory('equality')], [c_65, c_4725])).
% 8.09/3.32  tff(c_4961, plain, (![A_32, C_139]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_139))=C_139)), inference(demodulation, [status(thm), theory('equality')], [c_3207, c_3207, c_120, c_4916])).
% 8.09/3.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/3.32  tff(c_105, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 8.09/3.32  tff(c_293, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k5_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_105, c_284])).
% 8.09/3.32  tff(c_1410, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k4_xboole_0(A_1, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_293])).
% 8.09/3.32  tff(c_3212, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_1410])).
% 8.09/3.32  tff(c_6242, plain, (![B_157, A_158, C_159]: (k2_xboole_0(k4_xboole_0(B_157, k2_xboole_0(A_158, C_159)), k4_xboole_0(A_158, k2_xboole_0(B_157, C_159)))=k4_xboole_0(k5_xboole_0(A_158, B_157), C_159))), inference(superposition, [status(thm), theory('equality')], [c_846, c_2])).
% 8.09/3.32  tff(c_6366, plain, (![B_157, B_90]: (k2_xboole_0(k4_xboole_0(B_157, B_90), k4_xboole_0(B_90, k2_xboole_0(B_157, B_90)))=k4_xboole_0(k5_xboole_0(B_90, B_157), B_90))), inference(superposition, [status(thm), theory('equality')], [c_1940, c_6242])).
% 8.09/3.32  tff(c_6426, plain, (![B_90, B_157]: (k4_xboole_0(k5_xboole_0(B_90, B_157), B_90)=k4_xboole_0(B_157, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3212, c_6366])).
% 8.09/3.32  tff(c_433, plain, (![A_32]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_32), A_32)=k3_xboole_0(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_65, c_403])).
% 8.09/3.32  tff(c_480, plain, (![A_59]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_59), A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_433])).
% 8.09/3.32  tff(c_514, plain, (![B_15]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, B_15), k4_xboole_0(B_15, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_480])).
% 8.09/3.32  tff(c_523, plain, (![B_15]: (k5_xboole_0(B_15, k4_xboole_0(B_15, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_514])).
% 8.09/3.32  tff(c_442, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, k1_xboole_0), A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_403])).
% 8.09/3.32  tff(c_451, plain, (![A_5]: (k5_xboole_0(k4_xboole_0(A_5, k1_xboole_0), A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_305, c_10, c_442])).
% 8.09/3.32  tff(c_2696, plain, (![A_102, C_103]: (k5_xboole_0(k4_xboole_0(A_102, k1_xboole_0), k5_xboole_0(A_102, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_451, c_524])).
% 8.09/3.32  tff(c_2782, plain, (![B_15]: (k5_xboole_0(k4_xboole_0(B_15, k1_xboole_0), k1_xboole_0)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_15, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_523, c_2696])).
% 8.09/3.32  tff(c_2839, plain, (![B_104]: (k4_xboole_0(k4_xboole_0(B_104, k1_xboole_0), k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_305, c_65, c_16, c_2782])).
% 8.09/3.32  tff(c_2865, plain, (![B_104]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_104, k1_xboole_0))=k5_xboole_0(k1_xboole_0, B_104))), inference(superposition, [status(thm), theory('equality')], [c_2839, c_16])).
% 8.09/3.32  tff(c_2916, plain, (![B_104]: (k5_xboole_0(k1_xboole_0, B_104)=k4_xboole_0(B_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_2865])).
% 8.09/3.32  tff(c_3291, plain, (![B_104]: (k4_xboole_0(B_104, k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_3207, c_2916])).
% 8.09/3.32  tff(c_933, plain, (![A_5, B_71]: (k2_xboole_0(k4_xboole_0(A_5, k2_xboole_0(B_71, k1_xboole_0)), k4_xboole_0(B_71, A_5))=k4_xboole_0(k5_xboole_0(A_5, B_71), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_846])).
% 8.09/3.32  tff(c_945, plain, (![A_5, B_71]: (k2_xboole_0(k4_xboole_0(A_5, B_71), k4_xboole_0(B_71, A_5))=k4_xboole_0(k5_xboole_0(A_5, B_71), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_933])).
% 8.09/3.32  tff(c_3965, plain, (![A_5, B_71]: (k2_xboole_0(k4_xboole_0(A_5, B_71), k4_xboole_0(B_71, A_5))=k5_xboole_0(A_5, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_945])).
% 8.09/3.32  tff(c_4566, plain, (![A_133, B_134]: (k4_xboole_0(A_133, k2_xboole_0(B_134, A_133))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_1410])).
% 8.09/3.32  tff(c_9151, plain, (![B_195, A_196]: (k4_xboole_0(k4_xboole_0(B_195, A_196), k5_xboole_0(A_196, B_195))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3965, c_4566])).
% 8.09/3.32  tff(c_9206, plain, (![B_157, B_90]: (k4_xboole_0(k4_xboole_0(B_157, B_90), k5_xboole_0(B_90, k5_xboole_0(B_90, B_157)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6426, c_9151])).
% 8.09/3.32  tff(c_9335, plain, (![B_197, B_198]: (k4_xboole_0(k4_xboole_0(B_197, B_198), B_197)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4961, c_9206])).
% 8.09/3.32  tff(c_9424, plain, (![B_197, B_198]: (k2_xboole_0(B_197, k4_xboole_0(B_197, B_198))=k5_xboole_0(B_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9335, c_16])).
% 8.09/3.32  tff(c_9486, plain, (![B_197, B_198]: (k2_xboole_0(B_197, k4_xboole_0(B_197, B_198))=B_197)), inference(demodulation, [status(thm), theory('equality')], [c_3209, c_9424])).
% 8.09/3.32  tff(c_12, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/3.32  tff(c_3484, plain, (![A_112]: (k5_xboole_0(A_112, A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_299])).
% 8.09/3.32  tff(c_3529, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k5_xboole_0(B_10, k5_xboole_0(A_9, B_10)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_3484])).
% 8.09/3.32  tff(c_4964, plain, (![A_140, C_141]: (k5_xboole_0(A_140, k5_xboole_0(A_140, C_141))=C_141)), inference(demodulation, [status(thm), theory('equality')], [c_3207, c_3207, c_120, c_4916])).
% 8.09/3.32  tff(c_5067, plain, (![B_10, A_9]: (k5_xboole_0(B_10, k5_xboole_0(A_9, B_10))=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3529, c_4964])).
% 8.09/3.32  tff(c_5275, plain, (![B_144, A_145]: (k5_xboole_0(B_144, k5_xboole_0(A_145, B_144))=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_3209, c_5067])).
% 8.09/3.32  tff(c_5284, plain, (![B_144, A_145]: (k5_xboole_0(B_144, A_145)=k5_xboole_0(A_145, B_144))), inference(superposition, [status(thm), theory('equality')], [c_5275, c_4961])).
% 8.09/3.32  tff(c_4615, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4566])).
% 8.09/3.32  tff(c_5123, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k4_xboole_0(B_15, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4964])).
% 8.09/3.32  tff(c_5950, plain, (![A_152, A_153, B_154]: (k2_xboole_0(k4_xboole_0(A_152, k2_xboole_0(A_153, B_154)), k4_xboole_0(B_154, k2_xboole_0(A_152, A_153)))=k4_xboole_0(k5_xboole_0(A_152, B_154), A_153))), inference(superposition, [status(thm), theory('equality')], [c_2, c_846])).
% 8.09/3.32  tff(c_6055, plain, (![A_152, B_90]: (k2_xboole_0(k4_xboole_0(A_152, B_90), k4_xboole_0(B_90, k2_xboole_0(A_152, B_90)))=k4_xboole_0(k5_xboole_0(A_152, B_90), B_90))), inference(superposition, [status(thm), theory('equality')], [c_1940, c_5950])).
% 8.09/3.32  tff(c_7023, plain, (![A_167, B_168]: (k4_xboole_0(k5_xboole_0(A_167, B_168), B_168)=k4_xboole_0(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3212, c_6055])).
% 8.09/3.32  tff(c_7101, plain, (![B_15, A_14]: (k4_xboole_0(k4_xboole_0(B_15, A_14), k2_xboole_0(A_14, B_15))=k4_xboole_0(A_14, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_5123, c_7023])).
% 8.09/3.32  tff(c_12285, plain, (![B_231, A_232]: (k4_xboole_0(k4_xboole_0(B_231, A_232), k2_xboole_0(A_232, B_231))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4615, c_7101])).
% 8.09/3.32  tff(c_870, plain, (![B_71, A_70, C_72]: (k2_xboole_0(k4_xboole_0(B_71, k2_xboole_0(A_70, C_72)), k4_xboole_0(A_70, k2_xboole_0(B_71, C_72)))=k4_xboole_0(k5_xboole_0(A_70, B_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_846, c_2])).
% 8.09/3.32  tff(c_12341, plain, (![A_232, B_231]: (k2_xboole_0(k4_xboole_0(A_232, k2_xboole_0(k4_xboole_0(B_231, A_232), B_231)), k1_xboole_0)=k4_xboole_0(k5_xboole_0(k4_xboole_0(B_231, A_232), A_232), B_231))), inference(superposition, [status(thm), theory('equality')], [c_12285, c_870])).
% 8.09/3.32  tff(c_12494, plain, (![A_232, B_231]: (k4_xboole_0(k2_xboole_0(A_232, B_231), B_231)=k4_xboole_0(A_232, B_231))), inference(demodulation, [status(thm), theory('equality')], [c_9486, c_16, c_5284, c_2, c_6, c_12341])).
% 8.09/3.32  tff(c_28, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.09/3.32  tff(c_14675, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12494, c_28])).
% 8.09/3.32  tff(c_14916, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_14675])).
% 8.09/3.32  tff(c_14920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_14916])).
% 8.09/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.32  
% 8.09/3.32  Inference rules
% 8.09/3.32  ----------------------
% 8.09/3.32  #Ref     : 0
% 8.09/3.32  #Sup     : 3821
% 8.09/3.32  #Fact    : 0
% 8.09/3.32  #Define  : 0
% 8.09/3.32  #Split   : 1
% 8.09/3.32  #Chain   : 0
% 8.09/3.32  #Close   : 0
% 8.09/3.32  
% 8.09/3.32  Ordering : KBO
% 8.09/3.32  
% 8.09/3.32  Simplification rules
% 8.09/3.32  ----------------------
% 8.09/3.32  #Subsume      : 109
% 8.09/3.32  #Demod        : 4336
% 8.09/3.32  #Tautology    : 1823
% 8.09/3.32  #SimpNegUnit  : 1
% 8.09/3.32  #BackRed      : 26
% 8.09/3.32  
% 8.09/3.32  #Partial instantiations: 0
% 8.09/3.32  #Strategies tried      : 1
% 8.09/3.32  
% 8.09/3.32  Timing (in seconds)
% 8.09/3.32  ----------------------
% 8.09/3.32  Preprocessing        : 0.36
% 8.09/3.32  Parsing              : 0.20
% 8.09/3.32  CNF conversion       : 0.02
% 8.09/3.32  Main loop            : 2.19
% 8.09/3.32  Inferencing          : 0.53
% 8.09/3.32  Reduction            : 1.17
% 8.09/3.32  Demodulation         : 1.03
% 8.09/3.32  BG Simplification    : 0.09
% 8.09/3.32  Subsumption          : 0.29
% 8.09/3.32  Abstraction          : 0.13
% 8.09/3.32  MUC search           : 0.00
% 8.09/3.32  Cooper               : 0.00
% 8.09/3.32  Total                : 2.59
% 8.09/3.32  Index Insertion      : 0.00
% 8.09/3.32  Index Deletion       : 0.00
% 8.09/3.32  Index Matching       : 0.00
% 8.09/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
