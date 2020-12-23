%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:00 EST 2020

% Result     : Theorem 44.45s
% Output     : CNFRefutation 44.45s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 378 expanded)
%              Number of leaves         :   29 ( 142 expanded)
%              Depth                    :   25
%              Number of atoms          :  160 ( 624 expanded)
%              Number of equality atoms :   60 ( 234 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_190,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k10_relat_1(B_45,A_46),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [B_45,A_46] :
      ( k2_xboole_0(k10_relat_1(B_45,A_46),k1_relat_1(B_45)) = k1_relat_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_190,c_8])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_60,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_60])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [C_23,A_21,B_22] :
      ( k6_subset_1(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k6_subset_1(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_849,plain,(
    ! [C_94,A_95,B_96] :
      ( k4_xboole_0(k10_relat_1(C_94,A_95),k10_relat_1(C_94,B_96)) = k10_relat_1(C_94,k4_xboole_0(A_95,B_96))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_22])).

tff(c_877,plain,(
    ! [C_94,B_96] :
      ( k10_relat_1(C_94,k4_xboole_0(B_96,B_96)) = k1_xboole_0
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_67])).

tff(c_993,plain,(
    ! [C_102] :
      ( k10_relat_1(C_102,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_877])).

tff(c_996,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_993])).

tff(c_999,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_996])).

tff(c_18,plain,(
    ! [C_17,A_15,B_16] :
      ( k2_xboole_0(k10_relat_1(C_17,A_15),k10_relat_1(C_17,B_16)) = k10_relat_1(C_17,k2_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1012,plain,(
    ! [A_15] :
      ( k2_xboole_0(k10_relat_1('#skF_2',A_15),k1_xboole_0) = k10_relat_1('#skF_2',k2_xboole_0(A_15,k1_xboole_0))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_18])).

tff(c_1193,plain,(
    ! [A_107] : k2_xboole_0(k10_relat_1('#skF_2',A_107),k1_xboole_0) = k10_relat_1('#skF_2',k2_xboole_0(A_107,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1012])).

tff(c_252,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_273,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(resolution,[status(thm)],[c_49,c_252])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_293,plain,(
    ! [A_3,B_4,B_55] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_55)) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_3876,plain,(
    ! [A_164,B_165] : r1_tarski(k10_relat_1('#skF_2',A_164),k2_xboole_0(k10_relat_1('#skF_2',k2_xboole_0(A_164,k1_xboole_0)),B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_293])).

tff(c_3920,plain,(
    ! [A_164] :
      ( r1_tarski(k10_relat_1('#skF_2',A_164),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_3876])).

tff(c_3989,plain,(
    ! [A_166] : r1_tarski(k10_relat_1('#skF_2',A_166),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3920])).

tff(c_4128,plain,(
    ! [A_168] : k2_xboole_0(k10_relat_1('#skF_2',A_168),k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3989,c_8])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_338,plain,(
    ! [A_58,B_59,B_60] : r1_tarski(A_58,k2_xboole_0(k2_xboole_0(A_58,B_59),B_60)) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_351,plain,(
    ! [A_8,B_9,B_60] : r1_tarski(k4_xboole_0(A_8,B_9),k2_xboole_0(A_8,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_338])).

tff(c_4161,plain,(
    ! [A_168,B_9] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',A_168),B_9),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4128,c_351])).

tff(c_78,plain,(
    ! [A_38] : k4_xboole_0(A_38,A_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_60])).

tff(c_83,plain,(
    ! [A_38] : r1_tarski(k1_xboole_0,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_463,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(A_69,B_70) = B_70
      | k4_xboole_0(A_69,B_70) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_173])).

tff(c_487,plain,(
    ! [A_71] :
      ( k2_xboole_0(A_71,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_463])).

tff(c_509,plain,(
    ! [A_71,C_5] :
      ( r1_tarski(A_71,C_5)
      | ~ r1_tarski(k1_xboole_0,C_5)
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_6])).

tff(c_589,plain,(
    ! [A_75,C_76] :
      ( r1_tarski(A_75,C_76)
      | k1_xboole_0 != A_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_509])).

tff(c_604,plain,(
    ! [A_75,C_76] :
      ( k2_xboole_0(A_75,C_76) = C_76
      | k1_xboole_0 != A_75 ) ),
    inference(resolution,[status(thm)],[c_589,c_8])).

tff(c_272,plain,(
    ! [A_51,B_53] : r1_tarski(A_51,k2_xboole_0(A_51,B_53)) ),
    inference(resolution,[status(thm)],[c_49,c_252])).

tff(c_1318,plain,(
    ! [A_110] : r1_tarski(k10_relat_1('#skF_2',A_110),k10_relat_1('#skF_2',k2_xboole_0(A_110,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_272])).

tff(c_1334,plain,(
    ! [A_75] :
      ( r1_tarski(k10_relat_1('#skF_2',A_75),k10_relat_1('#skF_2',k1_xboole_0))
      | k1_xboole_0 != A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1318])).

tff(c_1350,plain,(
    ! [A_111] :
      ( r1_tarski(k10_relat_1('#skF_2',A_111),k1_xboole_0)
      | k1_xboole_0 != A_111 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1334])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1356,plain,(
    ! [A_111] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_111),k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_111 ) ),
    inference(resolution,[status(thm)],[c_1350,c_4])).

tff(c_1366,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1356])).

tff(c_30,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [C_20,A_18,B_19] :
      ( k6_subset_1(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19)) = k9_relat_1(C_20,k6_subset_1(A_18,B_19))
      | ~ v2_funct_1(C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [C_20,A_18,B_19] :
      ( k4_xboole_0(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19)) = k9_relat_1(C_20,k4_xboole_0(A_18,B_19))
      | ~ v2_funct_1(C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_1368,plain,(
    ! [A_112] :
      ( k10_relat_1('#skF_2',A_112) = k1_xboole_0
      | k1_xboole_0 != A_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1356])).

tff(c_35,plain,(
    ! [C_23,A_21,B_22] :
      ( k4_xboole_0(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k4_xboole_0(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_22])).

tff(c_1392,plain,(
    ! [A_21,A_112] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_21),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_21,A_112))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_35])).

tff(c_36852,plain,(
    ! [A_568,A_569] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_568,A_569)) = k10_relat_1('#skF_2',A_568)
      | k1_xboole_0 != A_569 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_12,c_1392])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,k10_relat_1(B_25,A_24)),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37106,plain,(
    ! [A_568,A_569] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_568)),k4_xboole_0(A_568,A_569))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_569 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36852,c_24])).

tff(c_191350,plain,(
    ! [A_1548,A_1549] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1548)),k4_xboole_0(A_1548,A_1549))
      | k1_xboole_0 != A_1549 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_37106])).

tff(c_191833,plain,(
    ! [A_1550] : r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1550)),A_1550) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191350])).

tff(c_193801,plain,(
    ! [A_1554] : k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1554)),A_1554) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191833,c_4])).

tff(c_194431,plain,(
    ! [B_19] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_19)),B_19)) = k1_xboole_0
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_193801])).

tff(c_207228,plain,(
    ! [B_1599] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1599)),B_1599)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_194431])).

tff(c_557,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k10_relat_1(B_73,k9_relat_1(B_73,A_72)))
      | ~ r1_tarski(A_72,k1_relat_1(B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_570,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,k10_relat_1(B_73,k9_relat_1(B_73,A_72))) = k1_xboole_0
      | ~ r1_tarski(A_72,k1_relat_1(B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_557,c_4])).

tff(c_207318,plain,(
    ! [B_1599] :
      ( k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1599)),B_1599),k10_relat_1('#skF_2',k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1599)),B_1599),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207228,c_570])).

tff(c_207511,plain,(
    ! [B_1599] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1599)),B_1599) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4161,c_12,c_1366,c_207318])).

tff(c_69,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_77,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_28])).

tff(c_207566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207511,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.45/34.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.45/34.55  
% 44.45/34.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.45/34.55  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 44.45/34.55  
% 44.45/34.55  %Foreground sorts:
% 44.45/34.55  
% 44.45/34.55  
% 44.45/34.55  %Background operators:
% 44.45/34.55  
% 44.45/34.55  
% 44.45/34.55  %Foreground operators:
% 44.45/34.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 44.45/34.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 44.45/34.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.45/34.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 44.45/34.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.45/34.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.45/34.55  tff('#skF_2', type, '#skF_2': $i).
% 44.45/34.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 44.45/34.55  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 44.45/34.55  tff('#skF_1', type, '#skF_1': $i).
% 44.45/34.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.45/34.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 44.45/34.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 44.45/34.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.45/34.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.45/34.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 44.45/34.55  
% 44.45/34.57  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 44.45/34.57  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 44.45/34.57  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 44.45/34.57  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 44.45/34.57  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 44.45/34.57  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 44.45/34.57  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 44.45/34.57  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 44.45/34.57  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 44.45/34.57  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 44.45/34.57  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 44.45/34.57  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 44.45/34.57  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 44.45/34.57  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.45/34.57  tff(c_190, plain, (![B_45, A_46]: (r1_tarski(k10_relat_1(B_45, A_46), k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 44.45/34.57  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.45/34.57  tff(c_197, plain, (![B_45, A_46]: (k2_xboole_0(k10_relat_1(B_45, A_46), k1_relat_1(B_45))=k1_relat_1(B_45) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_190, c_8])).
% 44.45/34.57  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.45/34.57  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 44.45/34.57  tff(c_46, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.45/34.57  tff(c_49, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46])).
% 44.45/34.57  tff(c_60, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 44.45/34.57  tff(c_67, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_60])).
% 44.45/34.57  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 44.45/34.57  tff(c_22, plain, (![C_23, A_21, B_22]: (k6_subset_1(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k6_subset_1(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 44.45/34.57  tff(c_849, plain, (![C_94, A_95, B_96]: (k4_xboole_0(k10_relat_1(C_94, A_95), k10_relat_1(C_94, B_96))=k10_relat_1(C_94, k4_xboole_0(A_95, B_96)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_22])).
% 44.45/34.57  tff(c_877, plain, (![C_94, B_96]: (k10_relat_1(C_94, k4_xboole_0(B_96, B_96))=k1_xboole_0 | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_849, c_67])).
% 44.45/34.57  tff(c_993, plain, (![C_102]: (k10_relat_1(C_102, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_102) | ~v1_relat_1(C_102))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_877])).
% 44.45/34.57  tff(c_996, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_993])).
% 44.45/34.57  tff(c_999, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_996])).
% 44.45/34.57  tff(c_18, plain, (![C_17, A_15, B_16]: (k2_xboole_0(k10_relat_1(C_17, A_15), k10_relat_1(C_17, B_16))=k10_relat_1(C_17, k2_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 44.45/34.57  tff(c_1012, plain, (![A_15]: (k2_xboole_0(k10_relat_1('#skF_2', A_15), k1_xboole_0)=k10_relat_1('#skF_2', k2_xboole_0(A_15, k1_xboole_0)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_999, c_18])).
% 44.45/34.57  tff(c_1193, plain, (![A_107]: (k2_xboole_0(k10_relat_1('#skF_2', A_107), k1_xboole_0)=k10_relat_1('#skF_2', k2_xboole_0(A_107, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1012])).
% 44.45/34.57  tff(c_252, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.45/34.57  tff(c_273, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_49, c_252])).
% 44.45/34.57  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.45/34.57  tff(c_293, plain, (![A_3, B_4, B_55]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_55)))), inference(resolution, [status(thm)], [c_273, c_6])).
% 44.45/34.57  tff(c_3876, plain, (![A_164, B_165]: (r1_tarski(k10_relat_1('#skF_2', A_164), k2_xboole_0(k10_relat_1('#skF_2', k2_xboole_0(A_164, k1_xboole_0)), B_165)))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_293])).
% 44.45/34.57  tff(c_3920, plain, (![A_164]: (r1_tarski(k10_relat_1('#skF_2', A_164), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_3876])).
% 44.45/34.57  tff(c_3989, plain, (![A_166]: (r1_tarski(k10_relat_1('#skF_2', A_166), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3920])).
% 44.45/34.57  tff(c_4128, plain, (![A_168]: (k2_xboole_0(k10_relat_1('#skF_2', A_168), k1_relat_1('#skF_2'))=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3989, c_8])).
% 44.45/34.57  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.45/34.57  tff(c_173, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.45/34.57  tff(c_189, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_173])).
% 44.45/34.57  tff(c_338, plain, (![A_58, B_59, B_60]: (r1_tarski(A_58, k2_xboole_0(k2_xboole_0(A_58, B_59), B_60)))), inference(resolution, [status(thm)], [c_273, c_6])).
% 44.45/34.57  tff(c_351, plain, (![A_8, B_9, B_60]: (r1_tarski(k4_xboole_0(A_8, B_9), k2_xboole_0(A_8, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_338])).
% 44.45/34.57  tff(c_4161, plain, (![A_168, B_9]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', A_168), B_9), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4128, c_351])).
% 44.45/34.57  tff(c_78, plain, (![A_38]: (k4_xboole_0(A_38, A_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_60])).
% 44.45/34.57  tff(c_83, plain, (![A_38]: (r1_tarski(k1_xboole_0, A_38))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 44.45/34.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 44.45/34.57  tff(c_463, plain, (![A_69, B_70]: (k2_xboole_0(A_69, B_70)=B_70 | k4_xboole_0(A_69, B_70)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_173])).
% 44.45/34.57  tff(c_487, plain, (![A_71]: (k2_xboole_0(A_71, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_12, c_463])).
% 44.45/34.57  tff(c_509, plain, (![A_71, C_5]: (r1_tarski(A_71, C_5) | ~r1_tarski(k1_xboole_0, C_5) | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_487, c_6])).
% 44.45/34.57  tff(c_589, plain, (![A_75, C_76]: (r1_tarski(A_75, C_76) | k1_xboole_0!=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_509])).
% 44.45/34.57  tff(c_604, plain, (![A_75, C_76]: (k2_xboole_0(A_75, C_76)=C_76 | k1_xboole_0!=A_75)), inference(resolution, [status(thm)], [c_589, c_8])).
% 44.45/34.57  tff(c_272, plain, (![A_51, B_53]: (r1_tarski(A_51, k2_xboole_0(A_51, B_53)))), inference(resolution, [status(thm)], [c_49, c_252])).
% 44.45/34.57  tff(c_1318, plain, (![A_110]: (r1_tarski(k10_relat_1('#skF_2', A_110), k10_relat_1('#skF_2', k2_xboole_0(A_110, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_272])).
% 44.45/34.57  tff(c_1334, plain, (![A_75]: (r1_tarski(k10_relat_1('#skF_2', A_75), k10_relat_1('#skF_2', k1_xboole_0)) | k1_xboole_0!=A_75)), inference(superposition, [status(thm), theory('equality')], [c_604, c_1318])).
% 44.45/34.57  tff(c_1350, plain, (![A_111]: (r1_tarski(k10_relat_1('#skF_2', A_111), k1_xboole_0) | k1_xboole_0!=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_999, c_1334])).
% 44.45/34.57  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 44.45/34.57  tff(c_1356, plain, (![A_111]: (k4_xboole_0(k10_relat_1('#skF_2', A_111), k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_111)), inference(resolution, [status(thm)], [c_1350, c_4])).
% 44.45/34.57  tff(c_1366, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1356])).
% 44.45/34.57  tff(c_30, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.45/34.57  tff(c_20, plain, (![C_20, A_18, B_19]: (k6_subset_1(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19))=k9_relat_1(C_20, k6_subset_1(A_18, B_19)) | ~v2_funct_1(C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 44.45/34.57  tff(c_36, plain, (![C_20, A_18, B_19]: (k4_xboole_0(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19))=k9_relat_1(C_20, k4_xboole_0(A_18, B_19)) | ~v2_funct_1(C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 44.45/34.57  tff(c_1368, plain, (![A_112]: (k10_relat_1('#skF_2', A_112)=k1_xboole_0 | k1_xboole_0!=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1356])).
% 44.45/34.57  tff(c_35, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k4_xboole_0(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_22])).
% 44.45/34.57  tff(c_1392, plain, (![A_21, A_112]: (k4_xboole_0(k10_relat_1('#skF_2', A_21), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_21, A_112)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_112)), inference(superposition, [status(thm), theory('equality')], [c_1368, c_35])).
% 44.45/34.57  tff(c_36852, plain, (![A_568, A_569]: (k10_relat_1('#skF_2', k4_xboole_0(A_568, A_569))=k10_relat_1('#skF_2', A_568) | k1_xboole_0!=A_569)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_12, c_1392])).
% 44.45/34.57  tff(c_24, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, k10_relat_1(B_25, A_24)), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 44.45/34.57  tff(c_37106, plain, (![A_568, A_569]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_568)), k4_xboole_0(A_568, A_569)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_569)), inference(superposition, [status(thm), theory('equality')], [c_36852, c_24])).
% 44.45/34.57  tff(c_191350, plain, (![A_1548, A_1549]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1548)), k4_xboole_0(A_1548, A_1549)) | k1_xboole_0!=A_1549)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_37106])).
% 44.45/34.57  tff(c_191833, plain, (![A_1550]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1550)), A_1550))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191350])).
% 44.45/34.57  tff(c_193801, plain, (![A_1554]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1554)), A_1554)=k1_xboole_0)), inference(resolution, [status(thm)], [c_191833, c_4])).
% 44.45/34.57  tff(c_194431, plain, (![B_19]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_19)), B_19))=k1_xboole_0 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_193801])).
% 44.45/34.57  tff(c_207228, plain, (![B_1599]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1599)), B_1599))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_194431])).
% 44.45/34.57  tff(c_557, plain, (![A_72, B_73]: (r1_tarski(A_72, k10_relat_1(B_73, k9_relat_1(B_73, A_72))) | ~r1_tarski(A_72, k1_relat_1(B_73)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_77])).
% 44.45/34.57  tff(c_570, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k10_relat_1(B_73, k9_relat_1(B_73, A_72)))=k1_xboole_0 | ~r1_tarski(A_72, k1_relat_1(B_73)) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_557, c_4])).
% 44.45/34.57  tff(c_207318, plain, (![B_1599]: (k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1599)), B_1599), k10_relat_1('#skF_2', k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1599)), B_1599), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207228, c_570])).
% 44.45/34.57  tff(c_207511, plain, (![B_1599]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1599)), B_1599)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4161, c_12, c_1366, c_207318])).
% 44.45/34.57  tff(c_69, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 44.45/34.57  tff(c_28, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.45/34.57  tff(c_77, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_28])).
% 44.45/34.57  tff(c_207566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207511, c_77])).
% 44.45/34.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 44.45/34.57  
% 44.45/34.57  Inference rules
% 44.45/34.57  ----------------------
% 44.45/34.57  #Ref     : 0
% 44.45/34.57  #Sup     : 51464
% 44.45/34.57  #Fact    : 0
% 44.45/34.57  #Define  : 0
% 44.45/34.57  #Split   : 6
% 44.45/34.57  #Chain   : 0
% 44.45/34.57  #Close   : 0
% 44.45/34.57  
% 44.45/34.57  Ordering : KBO
% 44.45/34.57  
% 44.45/34.57  Simplification rules
% 44.45/34.57  ----------------------
% 44.45/34.57  #Subsume      : 12461
% 44.45/34.57  #Demod        : 42278
% 44.45/34.57  #Tautology    : 23534
% 44.45/34.57  #SimpNegUnit  : 2
% 44.45/34.57  #BackRed      : 5
% 44.45/34.57  
% 44.45/34.57  #Partial instantiations: 0
% 44.45/34.57  #Strategies tried      : 1
% 44.45/34.57  
% 44.45/34.57  Timing (in seconds)
% 44.45/34.57  ----------------------
% 44.45/34.57  Preprocessing        : 0.31
% 44.45/34.57  Parsing              : 0.17
% 44.45/34.57  CNF conversion       : 0.02
% 44.45/34.57  Main loop            : 33.48
% 44.45/34.57  Inferencing          : 3.07
% 44.45/34.57  Reduction            : 16.25
% 44.45/34.57  Demodulation         : 14.10
% 44.45/34.57  BG Simplification    : 0.38
% 44.45/34.57  Subsumption          : 12.52
% 44.45/34.57  Abstraction          : 0.62
% 44.45/34.57  MUC search           : 0.00
% 44.45/34.57  Cooper               : 0.00
% 44.45/34.57  Total                : 33.83
% 44.45/34.57  Index Insertion      : 0.00
% 44.45/34.57  Index Deletion       : 0.00
% 44.45/34.57  Index Matching       : 0.00
% 44.45/34.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
