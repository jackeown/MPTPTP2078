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
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 24.66s
% Output     : CNFRefutation 24.80s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 419 expanded)
%              Number of leaves         :   27 ( 153 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 778 expanded)
%              Number of equality atoms :   50 ( 182 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [A_40,B_42] : r1_tarski(A_40,k2_xboole_0(A_40,B_42)) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_496,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k4_xboole_0(A_74,B_75),C_76)
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2085,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_xboole_0(k4_xboole_0(A_142,B_143),C_144) = C_144
      | ~ r1_tarski(A_142,k2_xboole_0(B_143,C_144)) ) ),
    inference(resolution,[status(thm)],[c_496,c_12])).

tff(c_2233,plain,(
    ! [A_145,B_146] : k2_xboole_0(k4_xboole_0(A_145,A_145),B_146) = B_146 ),
    inference(resolution,[status(thm)],[c_120,c_2085])).

tff(c_876,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(A_99,k2_xboole_0(B_100,C_101))
      | ~ r1_tarski(k4_xboole_0(A_99,B_100),C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_938,plain,(
    ! [A_99,B_100] : r1_tarski(A_99,k2_xboole_0(B_100,k4_xboole_0(A_99,B_100))) ),
    inference(resolution,[status(thm)],[c_6,c_876])).

tff(c_2541,plain,(
    ! [A_150,A_151] : r1_tarski(A_150,k4_xboole_0(A_150,k4_xboole_0(A_151,A_151))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_938])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_2582,plain,(
    ! [A_150,A_151] : k4_xboole_0(A_150,k4_xboole_0(A_151,A_151)) = A_150 ),
    inference(resolution,[status(thm)],[c_2541,c_99])).

tff(c_2347,plain,(
    ! [A_145,B_146] : r1_tarski(k4_xboole_0(A_145,A_145),B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_120])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    ! [C_25,A_23,B_24] :
      ( k4_xboole_0(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k4_xboole_0(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_24])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_121,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_140,plain,(
    ! [A_6,B_7,B_44] : r1_tarski(A_6,k2_xboole_0(k2_xboole_0(A_6,B_7),B_44)) ),
    inference(resolution,[status(thm)],[c_121,c_10])).

tff(c_3318,plain,(
    ! [A_166,B_167,B_168] : k2_xboole_0(k4_xboole_0(A_166,k2_xboole_0(A_166,B_167)),B_168) = B_168 ),
    inference(resolution,[status(thm)],[c_140,c_2085])).

tff(c_4673,plain,(
    ! [B_195] : k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),B_195) = B_195 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3318])).

tff(c_4814,plain,(
    ! [B_195] :
      ( k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_195) = B_195
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_4673])).

tff(c_4873,plain,(
    ! [B_195] : k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_195) = B_195 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4814])).

tff(c_2230,plain,(
    ! [A_40,B_42] : k2_xboole_0(k4_xboole_0(A_40,A_40),B_42) = B_42 ),
    inference(resolution,[status(thm)],[c_120,c_2085])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(k2_xboole_0(A_43,B_44),A_43) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_2313,plain,(
    ! [A_145,B_146] :
      ( k2_xboole_0(k4_xboole_0(A_145,A_145),B_146) = k4_xboole_0(A_145,A_145)
      | ~ r1_tarski(B_146,k4_xboole_0(A_145,A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_141])).

tff(c_9767,plain,(
    ! [A_281,B_282] :
      ( k4_xboole_0(A_281,A_281) = B_282
      | ~ r1_tarski(B_282,k4_xboole_0(A_281,A_281)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_2313])).

tff(c_9896,plain,(
    ! [A_284,A_283] : k4_xboole_0(A_284,A_284) = k4_xboole_0(A_283,A_283) ),
    inference(resolution,[status(thm)],[c_2347,c_9767])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10231,plain,(
    ! [A_283,A_284] :
      ( k2_xboole_0(A_283,k4_xboole_0(A_284,A_284)) = A_283
      | ~ r1_tarski(A_283,A_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9896,c_20])).

tff(c_10435,plain,(
    ! [A_285,A_286] : k2_xboole_0(A_285,k4_xboole_0(A_286,A_286)) = A_285 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10231])).

tff(c_13982,plain,(
    ! [A_312] : k4_xboole_0(A_312,A_312) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4873,c_10435])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1322,plain,(
    ! [B_117,A_118] :
      ( k9_relat_1(B_117,k10_relat_1(B_117,A_118)) = A_118
      | ~ r1_tarski(A_118,k2_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1353,plain,(
    ! [B_117,A_3,C_5] :
      ( k9_relat_1(B_117,k10_relat_1(B_117,k4_xboole_0(A_3,C_5))) = k4_xboole_0(A_3,C_5)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ r1_tarski(A_3,k2_relat_1(B_117)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1322])).

tff(c_14073,plain,(
    ! [A_312] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_312,A_312)) = k4_xboole_0('#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13982,c_1353])).

tff(c_14284,plain,(
    ! [A_312] : k9_relat_1('#skF_3',k4_xboole_0(A_312,A_312)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_34,c_14073])).

tff(c_2429,plain,(
    ! [A_147,B_148] : r1_tarski(k4_xboole_0(A_147,A_147),B_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_120])).

tff(c_2463,plain,(
    ! [A_147,B_12] : k4_xboole_0(k4_xboole_0(A_147,A_147),B_12) = k4_xboole_0(A_147,A_147) ),
    inference(resolution,[status(thm)],[c_2429,c_99])).

tff(c_10087,plain,(
    ! [A_284,B_12,A_283] : k4_xboole_0(k4_xboole_0(A_284,A_284),B_12) = k4_xboole_0(A_283,A_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_9896,c_2463])).

tff(c_182,plain,(
    ! [A_47,B_48,B_49] : r1_tarski(A_47,k2_xboole_0(k2_xboole_0(A_47,B_48),B_49)) ),
    inference(resolution,[status(thm)],[c_121,c_10])).

tff(c_198,plain,(
    ! [B_49] : r1_tarski(k10_relat_1('#skF_3','#skF_1'),k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_182])).

tff(c_1787,plain,(
    ! [C_131,A_132,B_133] :
      ( k4_xboole_0(k10_relat_1(C_131,A_132),k10_relat_1(C_131,B_133)) = k10_relat_1(C_131,k4_xboole_0(A_132,B_133))
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_24])).

tff(c_1820,plain,(
    ! [C_131,A_132,B_133,B_4] :
      ( r1_tarski(k10_relat_1(C_131,k4_xboole_0(A_132,B_133)),B_4)
      | ~ r1_tarski(k10_relat_1(C_131,A_132),B_4)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_8])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k4_xboole_0(A_13,B_14),C_15)
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10867,plain,(
    ! [C_287,A_288,B_289,C_290] :
      ( r1_tarski(k10_relat_1(C_287,k4_xboole_0(A_288,B_289)),C_290)
      | ~ r1_tarski(k10_relat_1(C_287,A_288),k2_xboole_0(k10_relat_1(C_287,B_289),C_290))
      | ~ v1_funct_1(C_287)
      | ~ v1_relat_1(C_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_16])).

tff(c_102750,plain,(
    ! [B_815,B_817,A_814,C_813,C_816] :
      ( r1_tarski(k10_relat_1(C_816,k4_xboole_0(k4_xboole_0(A_814,B_815),B_817)),C_813)
      | ~ r1_tarski(k10_relat_1(C_816,A_814),k2_xboole_0(k10_relat_1(C_816,B_817),C_813))
      | ~ v1_funct_1(C_816)
      | ~ v1_relat_1(C_816) ) ),
    inference(resolution,[status(thm)],[c_1820,c_10867])).

tff(c_102895,plain,(
    ! [B_815,B_49] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1',B_815),'#skF_2')),B_49)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_198,c_102750])).

tff(c_102959,plain,(
    ! [B_818,B_819] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1',B_818),'#skF_2')),B_819) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_102895])).

tff(c_103250,plain,(
    ! [A_820,B_821] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_820,A_820)),B_821) ),
    inference(superposition,[status(thm),theory(equality)],[c_10087,c_102959])).

tff(c_2413,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(A_145,A_145) = B_146
      | ~ r1_tarski(B_146,k4_xboole_0(A_145,A_145)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_2313])).

tff(c_9907,plain,(
    ! [A_283,B_146,A_284] :
      ( k4_xboole_0(A_283,A_283) = B_146
      | ~ r1_tarski(B_146,k4_xboole_0(A_284,A_284)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9896,c_2413])).

tff(c_105016,plain,(
    ! [A_831,A_832] : k4_xboole_0(A_831,A_831) = k10_relat_1('#skF_3',k4_xboole_0(A_832,A_832)) ),
    inference(resolution,[status(thm)],[c_103250,c_9907])).

tff(c_65,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_264,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_391,plain,(
    ! [A_66,B_67,B_68] :
      ( r1_tarski(A_66,k2_xboole_0(B_67,B_68))
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_140])).

tff(c_422,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_66,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_391])).

tff(c_1329,plain,(
    ! [A_66] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_66)) = A_66
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_66,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_422,c_1322])).

tff(c_1352,plain,(
    ! [A_66] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_66)) = A_66
      | ~ r1_tarski(A_66,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1329])).

tff(c_105330,plain,(
    ! [A_831,A_832] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_831,A_831)) = k4_xboole_0(A_832,A_832)
      | ~ r1_tarski(k4_xboole_0(A_832,A_832),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105016,c_1352])).

tff(c_106020,plain,(
    ! [A_833] : k4_xboole_0(A_833,A_833) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_14284,c_105330])).

tff(c_939,plain,(
    ! [A_102,B_103] : r1_tarski(A_102,k2_xboole_0(B_103,A_102)) ),
    inference(resolution,[status(thm)],[c_14,c_876])).

tff(c_991,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k2_xboole_0(B_103,A_102)) = k2_xboole_0(B_103,A_102) ),
    inference(resolution,[status(thm)],[c_939,c_12])).

tff(c_7223,plain,(
    ! [A_240,B_241,B_242] : r1_tarski(A_240,k2_xboole_0(B_241,k2_xboole_0(k4_xboole_0(A_240,B_241),B_242))) ),
    inference(resolution,[status(thm)],[c_120,c_876])).

tff(c_7394,plain,(
    ! [A_243,A_244] : r1_tarski(A_243,k2_xboole_0(k4_xboole_0(A_243,A_244),A_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_7223])).

tff(c_508,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_xboole_0(k4_xboole_0(A_74,B_75),C_76) = C_76
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(resolution,[status(thm)],[c_496,c_12])).

tff(c_7515,plain,(
    ! [A_245,A_246] : k2_xboole_0(k4_xboole_0(A_245,k4_xboole_0(A_245,A_246)),A_246) = A_246 ),
    inference(resolution,[status(thm)],[c_7394,c_508])).

tff(c_7650,plain,(
    ! [A_245,A_246] : r1_tarski(k4_xboole_0(A_245,k4_xboole_0(A_245,A_246)),A_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_7515,c_120])).

tff(c_106659,plain,(
    ! [A_833] : r1_tarski(k4_xboole_0('#skF_1',k4_xboole_0(A_833,A_833)),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106020,c_7650])).

tff(c_107064,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_106659])).

tff(c_107066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_107064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.36  % CPULimit   : 60
% 0.21/0.36  % DateTime   : Tue Dec  1 20:30:51 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.66/15.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.66/15.55  
% 24.66/15.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.66/15.56  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 24.66/15.56  
% 24.66/15.56  %Foreground sorts:
% 24.66/15.56  
% 24.66/15.56  
% 24.66/15.56  %Background operators:
% 24.66/15.56  
% 24.66/15.56  
% 24.66/15.56  %Foreground operators:
% 24.66/15.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.66/15.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.66/15.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.66/15.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.66/15.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.66/15.56  tff('#skF_2', type, '#skF_2': $i).
% 24.66/15.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.66/15.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 24.66/15.56  tff('#skF_3', type, '#skF_3': $i).
% 24.66/15.56  tff('#skF_1', type, '#skF_1': $i).
% 24.66/15.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.66/15.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 24.66/15.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.66/15.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.66/15.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.66/15.56  
% 24.80/15.58  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 24.80/15.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.80/15.58  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 24.80/15.58  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 24.80/15.58  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 24.80/15.58  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 24.80/15.58  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 24.80/15.58  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 24.80/15.58  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 24.80/15.58  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 24.80/15.58  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 24.80/15.58  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 24.80/15.58  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.80/15.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.80/15.58  tff(c_106, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.80/15.58  tff(c_120, plain, (![A_40, B_42]: (r1_tarski(A_40, k2_xboole_0(A_40, B_42)))), inference(resolution, [status(thm)], [c_6, c_106])).
% 24.80/15.58  tff(c_496, plain, (![A_74, B_75, C_76]: (r1_tarski(k4_xboole_0(A_74, B_75), C_76) | ~r1_tarski(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.80/15.58  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.80/15.58  tff(c_2085, plain, (![A_142, B_143, C_144]: (k2_xboole_0(k4_xboole_0(A_142, B_143), C_144)=C_144 | ~r1_tarski(A_142, k2_xboole_0(B_143, C_144)))), inference(resolution, [status(thm)], [c_496, c_12])).
% 24.80/15.58  tff(c_2233, plain, (![A_145, B_146]: (k2_xboole_0(k4_xboole_0(A_145, A_145), B_146)=B_146)), inference(resolution, [status(thm)], [c_120, c_2085])).
% 24.80/15.58  tff(c_876, plain, (![A_99, B_100, C_101]: (r1_tarski(A_99, k2_xboole_0(B_100, C_101)) | ~r1_tarski(k4_xboole_0(A_99, B_100), C_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 24.80/15.58  tff(c_938, plain, (![A_99, B_100]: (r1_tarski(A_99, k2_xboole_0(B_100, k4_xboole_0(A_99, B_100))))), inference(resolution, [status(thm)], [c_6, c_876])).
% 24.80/15.58  tff(c_2541, plain, (![A_150, A_151]: (r1_tarski(A_150, k4_xboole_0(A_150, k4_xboole_0(A_151, A_151))))), inference(superposition, [status(thm), theory('equality')], [c_2233, c_938])).
% 24.80/15.58  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.80/15.58  tff(c_89, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.80/15.58  tff(c_99, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_14, c_89])).
% 24.80/15.58  tff(c_2582, plain, (![A_150, A_151]: (k4_xboole_0(A_150, k4_xboole_0(A_151, A_151))=A_150)), inference(resolution, [status(thm)], [c_2541, c_99])).
% 24.80/15.58  tff(c_2347, plain, (![A_145, B_146]: (r1_tarski(k4_xboole_0(A_145, A_145), B_146))), inference(superposition, [status(thm), theory('equality')], [c_2233, c_120])).
% 24.80/15.58  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.80/15.58  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.80/15.58  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.80/15.58  tff(c_22, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.80/15.58  tff(c_24, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 24.80/15.58  tff(c_37, plain, (![C_25, A_23, B_24]: (k4_xboole_0(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k4_xboole_0(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_24])).
% 24.80/15.58  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.80/15.58  tff(c_50, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.80/15.58  tff(c_63, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_50])).
% 24.80/15.58  tff(c_121, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_6, c_106])).
% 24.80/15.58  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.80/15.58  tff(c_140, plain, (![A_6, B_7, B_44]: (r1_tarski(A_6, k2_xboole_0(k2_xboole_0(A_6, B_7), B_44)))), inference(resolution, [status(thm)], [c_121, c_10])).
% 24.80/15.58  tff(c_3318, plain, (![A_166, B_167, B_168]: (k2_xboole_0(k4_xboole_0(A_166, k2_xboole_0(A_166, B_167)), B_168)=B_168)), inference(resolution, [status(thm)], [c_140, c_2085])).
% 24.80/15.58  tff(c_4673, plain, (![B_195]: (k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), B_195)=B_195)), inference(superposition, [status(thm), theory('equality')], [c_63, c_3318])).
% 24.80/15.58  tff(c_4814, plain, (![B_195]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_195)=B_195 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_4673])).
% 24.80/15.58  tff(c_4873, plain, (![B_195]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_195)=B_195)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4814])).
% 24.80/15.58  tff(c_2230, plain, (![A_40, B_42]: (k2_xboole_0(k4_xboole_0(A_40, A_40), B_42)=B_42)), inference(resolution, [status(thm)], [c_120, c_2085])).
% 24.80/15.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.80/15.58  tff(c_141, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(k2_xboole_0(A_43, B_44), A_43))), inference(resolution, [status(thm)], [c_121, c_2])).
% 24.80/15.58  tff(c_2313, plain, (![A_145, B_146]: (k2_xboole_0(k4_xboole_0(A_145, A_145), B_146)=k4_xboole_0(A_145, A_145) | ~r1_tarski(B_146, k4_xboole_0(A_145, A_145)))), inference(superposition, [status(thm), theory('equality')], [c_2233, c_141])).
% 24.80/15.58  tff(c_9767, plain, (![A_281, B_282]: (k4_xboole_0(A_281, A_281)=B_282 | ~r1_tarski(B_282, k4_xboole_0(A_281, A_281)))), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_2313])).
% 24.80/15.58  tff(c_9896, plain, (![A_284, A_283]: (k4_xboole_0(A_284, A_284)=k4_xboole_0(A_283, A_283))), inference(resolution, [status(thm)], [c_2347, c_9767])).
% 24.80/15.58  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.80/15.58  tff(c_10231, plain, (![A_283, A_284]: (k2_xboole_0(A_283, k4_xboole_0(A_284, A_284))=A_283 | ~r1_tarski(A_283, A_283))), inference(superposition, [status(thm), theory('equality')], [c_9896, c_20])).
% 24.80/15.58  tff(c_10435, plain, (![A_285, A_286]: (k2_xboole_0(A_285, k4_xboole_0(A_286, A_286))=A_285)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10231])).
% 24.80/15.58  tff(c_13982, plain, (![A_312]: (k4_xboole_0(A_312, A_312)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4873, c_10435])).
% 24.80/15.58  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.80/15.58  tff(c_1322, plain, (![B_117, A_118]: (k9_relat_1(B_117, k10_relat_1(B_117, A_118))=A_118 | ~r1_tarski(A_118, k2_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.80/15.58  tff(c_1353, plain, (![B_117, A_3, C_5]: (k9_relat_1(B_117, k10_relat_1(B_117, k4_xboole_0(A_3, C_5)))=k4_xboole_0(A_3, C_5) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117) | ~r1_tarski(A_3, k2_relat_1(B_117)))), inference(resolution, [status(thm)], [c_8, c_1322])).
% 24.80/15.58  tff(c_14073, plain, (![A_312]: (k9_relat_1('#skF_3', k4_xboole_0(A_312, A_312))=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13982, c_1353])).
% 24.80/15.58  tff(c_14284, plain, (![A_312]: (k9_relat_1('#skF_3', k4_xboole_0(A_312, A_312))=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_34, c_14073])).
% 24.80/15.58  tff(c_2429, plain, (![A_147, B_148]: (r1_tarski(k4_xboole_0(A_147, A_147), B_148))), inference(superposition, [status(thm), theory('equality')], [c_2233, c_120])).
% 24.80/15.58  tff(c_2463, plain, (![A_147, B_12]: (k4_xboole_0(k4_xboole_0(A_147, A_147), B_12)=k4_xboole_0(A_147, A_147))), inference(resolution, [status(thm)], [c_2429, c_99])).
% 24.80/15.58  tff(c_10087, plain, (![A_284, B_12, A_283]: (k4_xboole_0(k4_xboole_0(A_284, A_284), B_12)=k4_xboole_0(A_283, A_283))), inference(superposition, [status(thm), theory('equality')], [c_9896, c_2463])).
% 24.80/15.58  tff(c_182, plain, (![A_47, B_48, B_49]: (r1_tarski(A_47, k2_xboole_0(k2_xboole_0(A_47, B_48), B_49)))), inference(resolution, [status(thm)], [c_121, c_10])).
% 24.80/15.58  tff(c_198, plain, (![B_49]: (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), B_49)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_182])).
% 24.80/15.58  tff(c_1787, plain, (![C_131, A_132, B_133]: (k4_xboole_0(k10_relat_1(C_131, A_132), k10_relat_1(C_131, B_133))=k10_relat_1(C_131, k4_xboole_0(A_132, B_133)) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_24])).
% 24.80/15.58  tff(c_1820, plain, (![C_131, A_132, B_133, B_4]: (r1_tarski(k10_relat_1(C_131, k4_xboole_0(A_132, B_133)), B_4) | ~r1_tarski(k10_relat_1(C_131, A_132), B_4) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_8])).
% 24.80/15.58  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(k4_xboole_0(A_13, B_14), C_15) | ~r1_tarski(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.80/15.58  tff(c_10867, plain, (![C_287, A_288, B_289, C_290]: (r1_tarski(k10_relat_1(C_287, k4_xboole_0(A_288, B_289)), C_290) | ~r1_tarski(k10_relat_1(C_287, A_288), k2_xboole_0(k10_relat_1(C_287, B_289), C_290)) | ~v1_funct_1(C_287) | ~v1_relat_1(C_287))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_16])).
% 24.80/15.58  tff(c_102750, plain, (![B_815, B_817, A_814, C_813, C_816]: (r1_tarski(k10_relat_1(C_816, k4_xboole_0(k4_xboole_0(A_814, B_815), B_817)), C_813) | ~r1_tarski(k10_relat_1(C_816, A_814), k2_xboole_0(k10_relat_1(C_816, B_817), C_813)) | ~v1_funct_1(C_816) | ~v1_relat_1(C_816))), inference(resolution, [status(thm)], [c_1820, c_10867])).
% 24.80/15.58  tff(c_102895, plain, (![B_815, B_49]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', B_815), '#skF_2')), B_49) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_198, c_102750])).
% 24.80/15.58  tff(c_102959, plain, (![B_818, B_819]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', B_818), '#skF_2')), B_819))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_102895])).
% 24.80/15.58  tff(c_103250, plain, (![A_820, B_821]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_820, A_820)), B_821))), inference(superposition, [status(thm), theory('equality')], [c_10087, c_102959])).
% 24.80/15.58  tff(c_2413, plain, (![A_145, B_146]: (k4_xboole_0(A_145, A_145)=B_146 | ~r1_tarski(B_146, k4_xboole_0(A_145, A_145)))), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_2313])).
% 24.80/15.58  tff(c_9907, plain, (![A_283, B_146, A_284]: (k4_xboole_0(A_283, A_283)=B_146 | ~r1_tarski(B_146, k4_xboole_0(A_284, A_284)))), inference(superposition, [status(thm), theory('equality')], [c_9896, c_2413])).
% 24.80/15.58  tff(c_105016, plain, (![A_831, A_832]: (k4_xboole_0(A_831, A_831)=k10_relat_1('#skF_3', k4_xboole_0(A_832, A_832)))), inference(resolution, [status(thm)], [c_103250, c_9907])).
% 24.80/15.58  tff(c_65, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_50])).
% 24.80/15.58  tff(c_264, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(B_61, A_60))=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.80/15.58  tff(c_391, plain, (![A_66, B_67, B_68]: (r1_tarski(A_66, k2_xboole_0(B_67, B_68)) | ~r1_tarski(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_264, c_140])).
% 24.80/15.58  tff(c_422, plain, (![A_66]: (r1_tarski(A_66, k2_relat_1('#skF_3')) | ~r1_tarski(A_66, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_391])).
% 24.80/15.58  tff(c_1329, plain, (![A_66]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_66))=A_66 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_66, '#skF_1'))), inference(resolution, [status(thm)], [c_422, c_1322])).
% 24.80/15.58  tff(c_1352, plain, (![A_66]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_66))=A_66 | ~r1_tarski(A_66, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1329])).
% 24.80/15.58  tff(c_105330, plain, (![A_831, A_832]: (k9_relat_1('#skF_3', k4_xboole_0(A_831, A_831))=k4_xboole_0(A_832, A_832) | ~r1_tarski(k4_xboole_0(A_832, A_832), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_105016, c_1352])).
% 24.80/15.58  tff(c_106020, plain, (![A_833]: (k4_xboole_0(A_833, A_833)=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_14284, c_105330])).
% 24.80/15.58  tff(c_939, plain, (![A_102, B_103]: (r1_tarski(A_102, k2_xboole_0(B_103, A_102)))), inference(resolution, [status(thm)], [c_14, c_876])).
% 24.80/15.58  tff(c_991, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k2_xboole_0(B_103, A_102))=k2_xboole_0(B_103, A_102))), inference(resolution, [status(thm)], [c_939, c_12])).
% 24.80/15.58  tff(c_7223, plain, (![A_240, B_241, B_242]: (r1_tarski(A_240, k2_xboole_0(B_241, k2_xboole_0(k4_xboole_0(A_240, B_241), B_242))))), inference(resolution, [status(thm)], [c_120, c_876])).
% 24.80/15.58  tff(c_7394, plain, (![A_243, A_244]: (r1_tarski(A_243, k2_xboole_0(k4_xboole_0(A_243, A_244), A_244)))), inference(superposition, [status(thm), theory('equality')], [c_991, c_7223])).
% 24.80/15.58  tff(c_508, plain, (![A_74, B_75, C_76]: (k2_xboole_0(k4_xboole_0(A_74, B_75), C_76)=C_76 | ~r1_tarski(A_74, k2_xboole_0(B_75, C_76)))), inference(resolution, [status(thm)], [c_496, c_12])).
% 24.80/15.58  tff(c_7515, plain, (![A_245, A_246]: (k2_xboole_0(k4_xboole_0(A_245, k4_xboole_0(A_245, A_246)), A_246)=A_246)), inference(resolution, [status(thm)], [c_7394, c_508])).
% 24.80/15.58  tff(c_7650, plain, (![A_245, A_246]: (r1_tarski(k4_xboole_0(A_245, k4_xboole_0(A_245, A_246)), A_246))), inference(superposition, [status(thm), theory('equality')], [c_7515, c_120])).
% 24.80/15.58  tff(c_106659, plain, (![A_833]: (r1_tarski(k4_xboole_0('#skF_1', k4_xboole_0(A_833, A_833)), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_106020, c_7650])).
% 24.80/15.58  tff(c_107064, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_106659])).
% 24.80/15.58  tff(c_107066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_107064])).
% 24.80/15.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.80/15.58  
% 24.80/15.58  Inference rules
% 24.80/15.58  ----------------------
% 24.80/15.58  #Ref     : 0
% 24.80/15.58  #Sup     : 26370
% 24.80/15.58  #Fact    : 0
% 24.80/15.58  #Define  : 0
% 24.80/15.58  #Split   : 6
% 24.80/15.58  #Chain   : 0
% 24.80/15.58  #Close   : 0
% 24.80/15.58  
% 24.80/15.58  Ordering : KBO
% 24.80/15.58  
% 24.80/15.58  Simplification rules
% 24.80/15.58  ----------------------
% 24.80/15.58  #Subsume      : 2965
% 24.80/15.58  #Demod        : 18674
% 24.80/15.58  #Tautology    : 13628
% 24.80/15.58  #SimpNegUnit  : 7
% 24.80/15.58  #BackRed      : 46
% 24.80/15.58  
% 24.80/15.58  #Partial instantiations: 0
% 24.80/15.58  #Strategies tried      : 1
% 24.80/15.58  
% 24.80/15.58  Timing (in seconds)
% 24.80/15.58  ----------------------
% 24.80/15.58  Preprocessing        : 0.30
% 24.80/15.58  Parsing              : 0.16
% 24.80/15.58  CNF conversion       : 0.02
% 24.80/15.58  Main loop            : 14.49
% 24.80/15.58  Inferencing          : 1.58
% 24.80/15.58  Reduction            : 8.28
% 24.80/15.58  Demodulation         : 7.50
% 24.80/15.58  BG Simplification    : 0.21
% 24.80/15.58  Subsumption          : 3.80
% 24.80/15.58  Abstraction          : 0.35
% 24.80/15.58  MUC search           : 0.00
% 24.80/15.58  Cooper               : 0.00
% 24.80/15.58  Total                : 14.84
% 24.80/15.58  Index Insertion      : 0.00
% 24.80/15.58  Index Deletion       : 0.00
% 24.80/15.58  Index Matching       : 0.00
% 24.80/15.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
