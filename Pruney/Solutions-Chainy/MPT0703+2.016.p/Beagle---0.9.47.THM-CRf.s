%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:10 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 196 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 355 expanded)
%              Number of equality atoms :   69 ( 136 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_55,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_32])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [B_46] : k4_xboole_0(B_46,B_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    ! [B_47] : r1_tarski(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_18])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [B_47] : k4_xboole_0(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_625,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(A_71,k3_xboole_0(B_72,C_73))
      | ~ r1_tarski(A_71,C_73)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5304,plain,(
    ! [A_200,B_201,C_202] :
      ( k4_xboole_0(A_200,k3_xboole_0(B_201,C_202)) = k1_xboole_0
      | ~ r1_tarski(A_200,C_202)
      | ~ r1_tarski(A_200,B_201) ) ),
    inference(resolution,[status(thm)],[c_625,c_10])).

tff(c_137,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_338,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_552,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = k3_xboole_0(B_70,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_338])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_570,plain,(
    ! [B_70] : k4_xboole_0(B_70,k3_xboole_0(B_70,B_70)) = k3_xboole_0(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_22])).

tff(c_5373,plain,(
    ! [C_202] :
      ( k3_xboole_0(C_202,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(C_202,C_202)
      | ~ r1_tarski(C_202,C_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5304,c_570])).

tff(c_5539,plain,(
    ! [C_202] : k3_xboole_0(C_202,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_5373])).

tff(c_382,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_338])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_254,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2006,plain,(
    ! [B_133,A_134] :
      ( B_133 = A_134
      | ~ r1_tarski(B_133,A_134)
      | k4_xboole_0(A_134,B_133) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_2072,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_2006])).

tff(c_2160,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = A_137
      | k3_xboole_0(A_137,B_138) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2072])).

tff(c_2310,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,B_2) = B_2
      | k3_xboole_0(B_2,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_2160])).

tff(c_5590,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5539,c_2310])).

tff(c_65,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1438,plain,(
    ! [A_110,B_111] :
      ( k2_xboole_0(A_110,B_111) = B_111
      | k4_xboole_0(A_110,B_111) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_1453,plain,(
    ! [B_2] :
      ( k2_xboole_0(B_2,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_1438])).

tff(c_6287,plain,(
    ! [B_206] :
      ( k2_xboole_0(B_206,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != B_206 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5590,c_1453])).

tff(c_393,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(k2_xboole_0(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_415,plain,(
    ! [A_59,B_4,B_61] :
      ( r1_tarski(A_59,B_4)
      | k4_xboole_0(k2_xboole_0(A_59,B_61),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_6337,plain,(
    ! [B_206,B_4] :
      ( r1_tarski(B_206,B_4)
      | k4_xboole_0(k1_xboole_0,B_4) != k1_xboole_0
      | k1_xboole_0 != B_206 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6287,c_415])).

tff(c_6485,plain,(
    ! [B_207,B_208] :
      ( r1_tarski(B_207,B_208)
      | k1_xboole_0 != B_207 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_6337])).

tff(c_270,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,k4_xboole_0(A_13,B_14)) ) ),
    inference(resolution,[status(thm)],[c_18,c_254])).

tff(c_8319,plain,(
    ! [B_14] : k4_xboole_0(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6485,c_270])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1217,plain,(
    ! [C_99,A_100,B_101] :
      ( k4_xboole_0(k10_relat_1(C_99,A_100),k10_relat_1(C_99,B_101)) = k10_relat_1(C_99,k4_xboole_0(A_100,B_101))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_1261,plain,(
    ! [C_99,A_100] :
      ( k10_relat_1(C_99,k4_xboole_0(A_100,A_100)) = k1_xboole_0
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1217])).

tff(c_1632,plain,(
    ! [C_116] :
      ( k10_relat_1(C_116,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1261])).

tff(c_1635,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1632])).

tff(c_1638,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1635])).

tff(c_877,plain,(
    ! [B_85,A_86] :
      ( k9_relat_1(B_85,k10_relat_1(B_85,A_86)) = A_86
      | ~ r1_tarski(A_86,k2_relat_1(B_85))
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8905,plain,(
    ! [B_240,A_241] :
      ( k9_relat_1(B_240,k10_relat_1(B_240,A_241)) = A_241
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240)
      | k4_xboole_0(A_241,k2_relat_1(B_240)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_877])).

tff(c_8930,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k1_xboole_0,k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_8905])).

tff(c_8953,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8319,c_40,c_38,c_8930])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_84,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_83,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_463,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(resolution,[status(thm)],[c_6,c_393])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_786,plain,(
    ! [A_79,B_80,B_81] : r1_tarski(A_79,k2_xboole_0(k2_xboole_0(A_79,B_80),B_81)) ),
    inference(resolution,[status(thm)],[c_463,c_12])).

tff(c_927,plain,(
    ! [A_88,B_89,B_90] : r1_tarski(k4_xboole_0(A_88,B_89),k2_xboole_0(A_88,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_786])).

tff(c_996,plain,(
    ! [B_91] : r1_tarski(k4_xboole_0('#skF_1',B_91),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_927])).

tff(c_1027,plain,(
    ! [B_91] : k4_xboole_0(k4_xboole_0('#skF_1',B_91),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_996,c_10])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_134,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_117])).

tff(c_1232,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_134])).

tff(c_1264,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1232])).

tff(c_8933,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_8905])).

tff(c_8955,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_40,c_38,c_8933])).

tff(c_8963,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8953,c_8955])).

tff(c_8964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.50  
% 6.04/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.04/2.50  
% 6.04/2.50  %Foreground sorts:
% 6.04/2.50  
% 6.04/2.50  
% 6.04/2.50  %Background operators:
% 6.04/2.50  
% 6.04/2.50  
% 6.04/2.50  %Foreground operators:
% 6.04/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.04/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.04/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.04/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.04/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.04/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.04/2.50  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.04/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.04/2.50  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.04/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.04/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.04/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.04/2.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.04/2.50  
% 6.38/2.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.38/2.52  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 6.38/2.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.38/2.52  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.38/2.52  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.38/2.52  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.38/2.52  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.38/2.52  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.38/2.52  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.38/2.52  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 6.38/2.52  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 6.38/2.52  tff(c_55, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.52  tff(c_32, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.38/2.52  tff(c_64, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_32])).
% 6.38/2.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.38/2.52  tff(c_117, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.52  tff(c_138, plain, (![B_46]: (k4_xboole_0(B_46, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_117])).
% 6.38/2.52  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.38/2.52  tff(c_154, plain, (![B_47]: (r1_tarski(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_138, c_18])).
% 6.38/2.52  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.52  tff(c_165, plain, (![B_47]: (k4_xboole_0(k1_xboole_0, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_10])).
% 6.38/2.52  tff(c_625, plain, (![A_71, B_72, C_73]: (r1_tarski(A_71, k3_xboole_0(B_72, C_73)) | ~r1_tarski(A_71, C_73) | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.38/2.52  tff(c_5304, plain, (![A_200, B_201, C_202]: (k4_xboole_0(A_200, k3_xboole_0(B_201, C_202))=k1_xboole_0 | ~r1_tarski(A_200, C_202) | ~r1_tarski(A_200, B_201))), inference(resolution, [status(thm)], [c_625, c_10])).
% 6.38/2.52  tff(c_137, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_117])).
% 6.38/2.52  tff(c_338, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.52  tff(c_552, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=k3_xboole_0(B_70, B_70))), inference(superposition, [status(thm), theory('equality')], [c_137, c_338])).
% 6.38/2.52  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.52  tff(c_570, plain, (![B_70]: (k4_xboole_0(B_70, k3_xboole_0(B_70, B_70))=k3_xboole_0(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_552, c_22])).
% 6.38/2.52  tff(c_5373, plain, (![C_202]: (k3_xboole_0(C_202, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(C_202, C_202) | ~r1_tarski(C_202, C_202))), inference(superposition, [status(thm), theory('equality')], [c_5304, c_570])).
% 6.38/2.52  tff(c_5539, plain, (![C_202]: (k3_xboole_0(C_202, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_5373])).
% 6.38/2.52  tff(c_382, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_137, c_338])).
% 6.38/2.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.52  tff(c_254, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.38/2.52  tff(c_2006, plain, (![B_133, A_134]: (B_133=A_134 | ~r1_tarski(B_133, A_134) | k4_xboole_0(A_134, B_133)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_254])).
% 6.38/2.52  tff(c_2072, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_2006])).
% 6.38/2.52  tff(c_2160, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)=A_137 | k3_xboole_0(A_137, B_138)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2072])).
% 6.38/2.52  tff(c_2310, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2 | k3_xboole_0(B_2, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_2160])).
% 6.38/2.52  tff(c_5590, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_5539, c_2310])).
% 6.38/2.52  tff(c_65, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.52  tff(c_1438, plain, (![A_110, B_111]: (k2_xboole_0(A_110, B_111)=B_111 | k4_xboole_0(A_110, B_111)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_65])).
% 6.38/2.52  tff(c_1453, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_1438])).
% 6.38/2.52  tff(c_6287, plain, (![B_206]: (k2_xboole_0(B_206, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=B_206)), inference(demodulation, [status(thm), theory('equality')], [c_5590, c_1453])).
% 6.38/2.52  tff(c_393, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.52  tff(c_415, plain, (![A_59, B_4, B_61]: (r1_tarski(A_59, B_4) | k4_xboole_0(k2_xboole_0(A_59, B_61), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_393])).
% 6.38/2.52  tff(c_6337, plain, (![B_206, B_4]: (r1_tarski(B_206, B_4) | k4_xboole_0(k1_xboole_0, B_4)!=k1_xboole_0 | k1_xboole_0!=B_206)), inference(superposition, [status(thm), theory('equality')], [c_6287, c_415])).
% 6.38/2.52  tff(c_6485, plain, (![B_207, B_208]: (r1_tarski(B_207, B_208) | k1_xboole_0!=B_207)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_6337])).
% 6.38/2.52  tff(c_270, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_18, c_254])).
% 6.38/2.52  tff(c_8319, plain, (![B_14]: (k4_xboole_0(k1_xboole_0, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6485, c_270])).
% 6.38/2.52  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.38/2.52  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.38/2.52  tff(c_24, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.38/2.52  tff(c_28, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.38/2.52  tff(c_1217, plain, (![C_99, A_100, B_101]: (k4_xboole_0(k10_relat_1(C_99, A_100), k10_relat_1(C_99, B_101))=k10_relat_1(C_99, k4_xboole_0(A_100, B_101)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 6.38/2.52  tff(c_1261, plain, (![C_99, A_100]: (k10_relat_1(C_99, k4_xboole_0(A_100, A_100))=k1_xboole_0 | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(superposition, [status(thm), theory('equality')], [c_137, c_1217])).
% 6.38/2.52  tff(c_1632, plain, (![C_116]: (k10_relat_1(C_116, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_116) | ~v1_relat_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1261])).
% 6.38/2.52  tff(c_1635, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1632])).
% 6.38/2.52  tff(c_1638, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1635])).
% 6.38/2.52  tff(c_877, plain, (![B_85, A_86]: (k9_relat_1(B_85, k10_relat_1(B_85, A_86))=A_86 | ~r1_tarski(A_86, k2_relat_1(B_85)) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.38/2.52  tff(c_8905, plain, (![B_240, A_241]: (k9_relat_1(B_240, k10_relat_1(B_240, A_241))=A_241 | ~v1_funct_1(B_240) | ~v1_relat_1(B_240) | k4_xboole_0(A_241, k2_relat_1(B_240))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_877])).
% 6.38/2.52  tff(c_8930, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k1_xboole_0, k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1638, c_8905])).
% 6.38/2.52  tff(c_8953, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8319, c_40, c_38, c_8930])).
% 6.38/2.52  tff(c_34, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.38/2.52  tff(c_84, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_65])).
% 6.38/2.52  tff(c_83, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), A_13)=A_13)), inference(resolution, [status(thm)], [c_18, c_65])).
% 6.38/2.52  tff(c_463, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(resolution, [status(thm)], [c_6, c_393])).
% 6.38/2.52  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.52  tff(c_786, plain, (![A_79, B_80, B_81]: (r1_tarski(A_79, k2_xboole_0(k2_xboole_0(A_79, B_80), B_81)))), inference(resolution, [status(thm)], [c_463, c_12])).
% 6.38/2.52  tff(c_927, plain, (![A_88, B_89, B_90]: (r1_tarski(k4_xboole_0(A_88, B_89), k2_xboole_0(A_88, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_786])).
% 6.38/2.52  tff(c_996, plain, (![B_91]: (r1_tarski(k4_xboole_0('#skF_1', B_91), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_927])).
% 6.38/2.52  tff(c_1027, plain, (![B_91]: (k4_xboole_0(k4_xboole_0('#skF_1', B_91), k2_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_996, c_10])).
% 6.38/2.52  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.38/2.52  tff(c_134, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_117])).
% 6.38/2.52  tff(c_1232, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1217, c_134])).
% 6.38/2.52  tff(c_1264, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1232])).
% 6.38/2.52  tff(c_8933, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1264, c_8905])).
% 6.38/2.52  tff(c_8955, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_40, c_38, c_8933])).
% 6.38/2.52  tff(c_8963, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8953, c_8955])).
% 6.38/2.52  tff(c_8964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_8963])).
% 6.38/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.52  
% 6.38/2.52  Inference rules
% 6.38/2.52  ----------------------
% 6.38/2.52  #Ref     : 0
% 6.38/2.52  #Sup     : 2191
% 6.38/2.52  #Fact    : 0
% 6.38/2.52  #Define  : 0
% 6.38/2.52  #Split   : 5
% 6.38/2.52  #Chain   : 0
% 6.38/2.52  #Close   : 0
% 6.38/2.52  
% 6.38/2.52  Ordering : KBO
% 6.38/2.52  
% 6.38/2.52  Simplification rules
% 6.38/2.52  ----------------------
% 6.38/2.52  #Subsume      : 237
% 6.38/2.52  #Demod        : 1536
% 6.38/2.52  #Tautology    : 1370
% 6.38/2.52  #SimpNegUnit  : 11
% 6.38/2.52  #BackRed      : 10
% 6.38/2.52  
% 6.38/2.52  #Partial instantiations: 0
% 6.38/2.52  #Strategies tried      : 1
% 6.38/2.52  
% 6.38/2.52  Timing (in seconds)
% 6.38/2.52  ----------------------
% 6.38/2.52  Preprocessing        : 0.45
% 6.38/2.52  Parsing              : 0.26
% 6.38/2.52  CNF conversion       : 0.02
% 6.38/2.52  Main loop            : 1.22
% 6.38/2.52  Inferencing          : 0.36
% 6.38/2.52  Reduction            : 0.52
% 6.38/2.52  Demodulation         : 0.41
% 6.38/2.52  BG Simplification    : 0.04
% 6.38/2.52  Subsumption          : 0.22
% 6.38/2.52  Abstraction          : 0.06
% 6.38/2.52  MUC search           : 0.00
% 6.38/2.52  Cooper               : 0.00
% 6.38/2.52  Total                : 1.71
% 6.38/2.52  Index Insertion      : 0.00
% 6.38/2.52  Index Deletion       : 0.00
% 6.38/2.52  Index Matching       : 0.00
% 6.38/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
