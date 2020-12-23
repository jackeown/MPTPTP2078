%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 30.12s
% Output     : CNFRefutation 30.33s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 415 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  189 ( 768 expanded)
%              Number of equality atoms :   53 ( 181 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_644,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(k4_xboole_0(A_85,B_86),C_87)
      | ~ r1_tarski(A_85,k2_xboole_0(B_86,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2748,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_xboole_0(k4_xboole_0(A_142,B_143),C_144) = C_144
      | ~ r1_tarski(A_142,k2_xboole_0(B_143,C_144)) ) ),
    inference(resolution,[status(thm)],[c_644,c_8])).

tff(c_2903,plain,(
    ! [A_145,B_146] : k2_xboole_0(k4_xboole_0(A_145,A_145),B_146) = B_146 ),
    inference(resolution,[status(thm)],[c_20,c_2748])).

tff(c_3035,plain,(
    ! [A_145,B_146] : r1_tarski(k4_xboole_0(A_145,A_145),B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_2903,c_20])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_974,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(k2_xboole_0(A_101,C_102),B_103)
      | ~ r1_tarski(C_102,B_103)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(k2_xboole_0(A_18,B_19),A_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_108])).

tff(c_986,plain,(
    ! [B_103,C_102] :
      ( k2_xboole_0(B_103,C_102) = B_103
      | ~ r1_tarski(C_102,B_103)
      | ~ r1_tarski(B_103,B_103) ) ),
    inference(resolution,[status(thm)],[c_974,c_121])).

tff(c_1036,plain,(
    ! [B_104,C_105] :
      ( k2_xboole_0(B_104,C_105) = B_104
      | ~ r1_tarski(C_105,B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_986])).

tff(c_1108,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3','#skF_1')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1036])).

tff(c_1337,plain,(
    ! [A_110,B_111] : k2_xboole_0(k2_xboole_0(A_110,B_111),A_110) = k2_xboole_0(A_110,B_111) ),
    inference(resolution,[status(thm)],[c_20,c_1036])).

tff(c_176,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_229,plain,(
    ! [A_55,A_56,B_57] :
      ( r1_tarski(A_55,A_56)
      | ~ r1_tarski(A_55,k4_xboole_0(A_56,B_57)) ) ),
    inference(resolution,[status(thm)],[c_12,c_176])).

tff(c_238,plain,(
    ! [A_56,B_57,B_9] : r1_tarski(k4_xboole_0(k4_xboole_0(A_56,B_57),B_9),A_56) ),
    inference(resolution,[status(thm)],[c_12,c_229])).

tff(c_277,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(A_64,k2_xboole_0(B_65,C_66))
      | ~ r1_tarski(k4_xboole_0(A_64,B_65),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_366,plain,(
    ! [A_71,B_72,B_73] : r1_tarski(k4_xboole_0(A_71,B_72),k2_xboole_0(B_73,A_71)) ),
    inference(resolution,[status(thm)],[c_238,c_277])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k2_xboole_0(B_14,C_15))
      | ~ r1_tarski(k4_xboole_0(A_13,B_14),C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_395,plain,(
    ! [A_71,B_72,B_73] : r1_tarski(A_71,k2_xboole_0(B_72,k2_xboole_0(B_73,A_71))) ),
    inference(resolution,[status(thm)],[c_366,c_16])).

tff(c_1377,plain,(
    ! [A_71,B_73,B_111] : r1_tarski(A_71,k2_xboole_0(k2_xboole_0(B_73,A_71),B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1337,c_395])).

tff(c_11340,plain,(
    ! [A_256,B_257,B_258] : k2_xboole_0(k4_xboole_0(A_256,k2_xboole_0(B_257,A_256)),B_258) = B_258 ),
    inference(resolution,[status(thm)],[c_1377,c_2748])).

tff(c_2901,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,A_18),B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_20,c_2748])).

tff(c_1110,plain,(
    ! [A_18,B_19] : k2_xboole_0(k2_xboole_0(A_18,B_19),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(resolution,[status(thm)],[c_20,c_1036])).

tff(c_2939,plain,(
    ! [A_145,B_146] : k2_xboole_0(k4_xboole_0(A_145,A_145),B_146) = k2_xboole_0(B_146,k4_xboole_0(A_145,A_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2903,c_1110])).

tff(c_3088,plain,(
    ! [B_146,A_145] : k2_xboole_0(B_146,k4_xboole_0(A_145,A_145)) = B_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2939])).

tff(c_13277,plain,(
    ! [A_282,A_280,B_281] : k4_xboole_0(A_282,A_282) = k4_xboole_0(A_280,k2_xboole_0(B_281,A_280)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11340,c_3088])).

tff(c_20520,plain,(
    ! [A_332] : k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k4_xboole_0(A_332,A_332) ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_13277])).

tff(c_24,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [C_27,A_25,B_26] :
      ( k6_subset_1(k10_relat_1(C_27,A_25),k10_relat_1(C_27,B_26)) = k10_relat_1(C_27,k6_subset_1(A_25,B_26))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_39,plain,(
    ! [C_27,A_25,B_26] :
      ( k4_xboole_0(k10_relat_1(C_27,A_25),k10_relat_1(C_27,B_26)) = k10_relat_1(C_27,k4_xboole_0(A_25,B_26))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_20720,plain,(
    ! [A_332] :
      ( k4_xboole_0(A_332,A_332) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20520,c_39])).

tff(c_22351,plain,(
    ! [A_344] : k4_xboole_0(A_344,A_344) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_20720])).

tff(c_190,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_48,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_176])).

tff(c_1508,plain,(
    ! [B_113,A_114] :
      ( k9_relat_1(B_113,k10_relat_1(B_113,A_114)) = A_114
      | ~ r1_tarski(A_114,k2_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1521,plain,(
    ! [A_48] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_48)) = A_48
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_48,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_190,c_1508])).

tff(c_1538,plain,(
    ! [A_48] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_48)) = A_48
      | ~ r1_tarski(A_48,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1521])).

tff(c_22391,plain,(
    ! [A_344] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_344,A_344)) = k4_xboole_0('#skF_1','#skF_2')
      | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22351,c_1538])).

tff(c_22665,plain,(
    ! [A_344] : k9_relat_1('#skF_3',k4_xboole_0(A_344,A_344)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22391])).

tff(c_3161,plain,(
    ! [B_149,A_150] : k2_xboole_0(B_149,k4_xboole_0(A_150,A_150)) = B_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2939])).

tff(c_3296,plain,(
    ! [A_18,A_150] : k4_xboole_0(A_18,A_18) = k4_xboole_0(A_150,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2901,c_3161])).

tff(c_1109,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_1036])).

tff(c_5836,plain,(
    ! [A_186,B_187] : k4_xboole_0(k4_xboole_0(A_186,A_186),B_187) = k4_xboole_0(A_186,A_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_2903])).

tff(c_5980,plain,(
    ! [A_150,B_187,A_18] : k4_xboole_0(k4_xboole_0(A_150,A_150),B_187) = k4_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_5836])).

tff(c_300,plain,(
    ! [A_56,B_57,B_9] : r1_tarski(k4_xboole_0(A_56,B_57),k2_xboole_0(B_9,A_56)) ),
    inference(resolution,[status(thm)],[c_238,c_277])).

tff(c_3390,plain,(
    ! [B_151] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),B_151),k10_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_300])).

tff(c_3407,plain,(
    ! [B_26] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_26)),k10_relat_1('#skF_3','#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_3390])).

tff(c_36719,plain,(
    ! [B_441] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_441)),k10_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3407])).

tff(c_36784,plain,(
    ! [A_18] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_18,A_18)),k10_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_36719])).

tff(c_189,plain,(
    ! [A_48,A_18,B_19] :
      ( r1_tarski(A_48,k2_xboole_0(A_18,B_19))
      | ~ r1_tarski(A_48,A_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_176])).

tff(c_1915,plain,(
    ! [C_127,A_128,B_129] :
      ( k4_xboole_0(k10_relat_1(C_127,A_128),k10_relat_1(C_127,B_129)) = k10_relat_1(C_127,k4_xboole_0(A_128,B_129))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14573,plain,(
    ! [C_290,A_291,B_292,C_293] :
      ( r1_tarski(k10_relat_1(C_290,k4_xboole_0(A_291,B_292)),C_293)
      | ~ r1_tarski(k10_relat_1(C_290,A_291),k2_xboole_0(k10_relat_1(C_290,B_292),C_293))
      | ~ v1_funct_1(C_290)
      | ~ v1_relat_1(C_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_14])).

tff(c_133881,plain,(
    ! [C_913,A_914,B_915,B_916] :
      ( r1_tarski(k10_relat_1(C_913,k4_xboole_0(A_914,B_915)),B_916)
      | ~ v1_funct_1(C_913)
      | ~ v1_relat_1(C_913)
      | ~ r1_tarski(k10_relat_1(C_913,A_914),k10_relat_1(C_913,B_915)) ) ),
    inference(resolution,[status(thm)],[c_189,c_14573])).

tff(c_133885,plain,(
    ! [A_18,B_916] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0(A_18,A_18),'#skF_2')),B_916)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36784,c_133881])).

tff(c_133936,plain,(
    ! [A_917,B_918] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_917,A_917)),B_918) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5980,c_133885])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8852,plain,(
    ! [A_224,B_225,C_226] :
      ( k4_xboole_0(A_224,B_225) = C_226
      | ~ r1_tarski(C_226,k4_xboole_0(A_224,B_225))
      | ~ r1_tarski(A_224,k2_xboole_0(B_225,C_226)) ) ),
    inference(resolution,[status(thm)],[c_644,c_2])).

tff(c_8891,plain,(
    ! [A_150,C_226,A_18] :
      ( k4_xboole_0(A_150,A_150) = C_226
      | ~ r1_tarski(C_226,k4_xboole_0(A_18,A_18))
      | ~ r1_tarski(A_150,k2_xboole_0(A_150,C_226)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_8852])).

tff(c_8942,plain,(
    ! [A_150,C_226,A_18] :
      ( k4_xboole_0(A_150,A_150) = C_226
      | ~ r1_tarski(C_226,k4_xboole_0(A_18,A_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8891])).

tff(c_134465,plain,(
    ! [A_920,A_921] : k4_xboole_0(A_920,A_920) = k10_relat_1('#skF_3',k4_xboole_0(A_921,A_921)) ),
    inference(resolution,[status(thm)],[c_133936,c_8942])).

tff(c_53,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_12173,plain,(
    ! [B_265,A_266,B_267] :
      ( k9_relat_1(B_265,k10_relat_1(B_265,k4_xboole_0(A_266,B_267))) = k4_xboole_0(A_266,B_267)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265)
      | ~ r1_tarski(A_266,k2_xboole_0(B_267,k2_relat_1(B_265))) ) ),
    inference(resolution,[status(thm)],[c_14,c_1508])).

tff(c_12297,plain,(
    ! [A_266] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k4_xboole_0(A_266,'#skF_1'))) = k4_xboole_0(A_266,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_266,k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_12173])).

tff(c_12348,plain,(
    ! [A_266] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k4_xboole_0(A_266,'#skF_1'))) = k4_xboole_0(A_266,'#skF_1')
      | ~ r1_tarski(A_266,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_12297])).

tff(c_134696,plain,(
    ! [A_920] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_920,A_920)) = k4_xboole_0('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134465,c_12348])).

tff(c_135306,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22665,c_134696])).

tff(c_306,plain,(
    ! [A_67,B_68] : r1_tarski(A_67,k2_xboole_0(B_68,A_67)) ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_339,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = k2_xboole_0(B_68,A_67) ),
    inference(resolution,[status(thm)],[c_306,c_8])).

tff(c_664,plain,(
    ! [A_88,B_89,B_90] : r1_tarski(A_88,k2_xboole_0(B_89,k2_xboole_0(k4_xboole_0(A_88,B_89),B_90))) ),
    inference(resolution,[status(thm)],[c_20,c_277])).

tff(c_683,plain,(
    ! [A_88,A_67] : r1_tarski(A_88,k2_xboole_0(k4_xboole_0(A_88,A_67),A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_664])).

tff(c_6392,plain,(
    ! [A_193,A_194] : k2_xboole_0(k4_xboole_0(A_193,k4_xboole_0(A_193,A_194)),A_194) = A_194 ),
    inference(resolution,[status(thm)],[c_683,c_2748])).

tff(c_6787,plain,(
    ! [A_198,A_199] : r1_tarski(k4_xboole_0(A_198,k4_xboole_0(A_198,A_199)),A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_6392,c_20])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1015,plain,(
    ! [B_17,B_103,A_16] :
      ( r1_tarski(B_17,B_103)
      | ~ r1_tarski(k4_xboole_0(B_17,A_16),B_103)
      | ~ r1_tarski(A_16,B_103)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_974])).

tff(c_6790,plain,(
    ! [A_198,A_199] :
      ( r1_tarski(A_198,A_199)
      | ~ r1_tarski(k4_xboole_0(A_198,A_199),A_199)
      | ~ r1_tarski(k4_xboole_0(A_198,A_199),A_198) ) ),
    inference(resolution,[status(thm)],[c_6787,c_1015])).

tff(c_6858,plain,(
    ! [A_198,A_199] :
      ( r1_tarski(A_198,A_199)
      | ~ r1_tarski(k4_xboole_0(A_198,A_199),A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6790])).

tff(c_135947,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135306,c_6858])).

tff(c_136089,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3035,c_135947])).

tff(c_136091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_136089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.12/20.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.12/20.48  
% 30.12/20.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.12/20.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 30.12/20.48  
% 30.12/20.48  %Foreground sorts:
% 30.12/20.48  
% 30.12/20.48  
% 30.12/20.48  %Background operators:
% 30.12/20.48  
% 30.12/20.48  
% 30.12/20.48  %Foreground operators:
% 30.12/20.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.12/20.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.12/20.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.12/20.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.12/20.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.12/20.48  tff('#skF_2', type, '#skF_2': $i).
% 30.12/20.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 30.12/20.48  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 30.12/20.48  tff('#skF_3', type, '#skF_3': $i).
% 30.12/20.48  tff('#skF_1', type, '#skF_1': $i).
% 30.12/20.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.12/20.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 30.12/20.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.12/20.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.12/20.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.12/20.49  
% 30.33/20.51  tff(f_90, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 30.33/20.51  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 30.33/20.51  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 30.33/20.51  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 30.33/20.51  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 30.33/20.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.33/20.51  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 30.33/20.51  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 30.33/20.51  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 30.33/20.51  tff(f_65, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 30.33/20.51  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 30.33/20.51  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 30.33/20.51  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 30.33/20.51  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 30.33/20.51  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.33/20.51  tff(c_644, plain, (![A_85, B_86, C_87]: (r1_tarski(k4_xboole_0(A_85, B_86), C_87) | ~r1_tarski(A_85, k2_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 30.33/20.51  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.33/20.51  tff(c_2748, plain, (![A_142, B_143, C_144]: (k2_xboole_0(k4_xboole_0(A_142, B_143), C_144)=C_144 | ~r1_tarski(A_142, k2_xboole_0(B_143, C_144)))), inference(resolution, [status(thm)], [c_644, c_8])).
% 30.33/20.51  tff(c_2903, plain, (![A_145, B_146]: (k2_xboole_0(k4_xboole_0(A_145, A_145), B_146)=B_146)), inference(resolution, [status(thm)], [c_20, c_2748])).
% 30.33/20.51  tff(c_3035, plain, (![A_145, B_146]: (r1_tarski(k4_xboole_0(A_145, A_145), B_146))), inference(superposition, [status(thm), theory('equality')], [c_2903, c_20])).
% 30.33/20.51  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 30.33/20.51  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.33/20.51  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 30.33/20.51  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 30.33/20.51  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 30.33/20.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.33/20.51  tff(c_974, plain, (![A_101, C_102, B_103]: (r1_tarski(k2_xboole_0(A_101, C_102), B_103) | ~r1_tarski(C_102, B_103) | ~r1_tarski(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.33/20.51  tff(c_108, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.33/20.51  tff(c_121, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(k2_xboole_0(A_18, B_19), A_18))), inference(resolution, [status(thm)], [c_20, c_108])).
% 30.33/20.51  tff(c_986, plain, (![B_103, C_102]: (k2_xboole_0(B_103, C_102)=B_103 | ~r1_tarski(C_102, B_103) | ~r1_tarski(B_103, B_103))), inference(resolution, [status(thm)], [c_974, c_121])).
% 30.33/20.51  tff(c_1036, plain, (![B_104, C_105]: (k2_xboole_0(B_104, C_105)=B_104 | ~r1_tarski(C_105, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_986])).
% 30.33/20.51  tff(c_1108, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', '#skF_1'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_1036])).
% 30.33/20.51  tff(c_1337, plain, (![A_110, B_111]: (k2_xboole_0(k2_xboole_0(A_110, B_111), A_110)=k2_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_20, c_1036])).
% 30.33/20.51  tff(c_176, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.33/20.51  tff(c_229, plain, (![A_55, A_56, B_57]: (r1_tarski(A_55, A_56) | ~r1_tarski(A_55, k4_xboole_0(A_56, B_57)))), inference(resolution, [status(thm)], [c_12, c_176])).
% 30.33/20.51  tff(c_238, plain, (![A_56, B_57, B_9]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_56, B_57), B_9), A_56))), inference(resolution, [status(thm)], [c_12, c_229])).
% 30.33/20.51  tff(c_277, plain, (![A_64, B_65, C_66]: (r1_tarski(A_64, k2_xboole_0(B_65, C_66)) | ~r1_tarski(k4_xboole_0(A_64, B_65), C_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.33/20.51  tff(c_366, plain, (![A_71, B_72, B_73]: (r1_tarski(k4_xboole_0(A_71, B_72), k2_xboole_0(B_73, A_71)))), inference(resolution, [status(thm)], [c_238, c_277])).
% 30.33/20.51  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k2_xboole_0(B_14, C_15)) | ~r1_tarski(k4_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.33/20.51  tff(c_395, plain, (![A_71, B_72, B_73]: (r1_tarski(A_71, k2_xboole_0(B_72, k2_xboole_0(B_73, A_71))))), inference(resolution, [status(thm)], [c_366, c_16])).
% 30.33/20.51  tff(c_1377, plain, (![A_71, B_73, B_111]: (r1_tarski(A_71, k2_xboole_0(k2_xboole_0(B_73, A_71), B_111)))), inference(superposition, [status(thm), theory('equality')], [c_1337, c_395])).
% 30.33/20.51  tff(c_11340, plain, (![A_256, B_257, B_258]: (k2_xboole_0(k4_xboole_0(A_256, k2_xboole_0(B_257, A_256)), B_258)=B_258)), inference(resolution, [status(thm)], [c_1377, c_2748])).
% 30.33/20.51  tff(c_2901, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, A_18), B_19)=B_19)), inference(resolution, [status(thm)], [c_20, c_2748])).
% 30.33/20.51  tff(c_1110, plain, (![A_18, B_19]: (k2_xboole_0(k2_xboole_0(A_18, B_19), A_18)=k2_xboole_0(A_18, B_19))), inference(resolution, [status(thm)], [c_20, c_1036])).
% 30.33/20.51  tff(c_2939, plain, (![A_145, B_146]: (k2_xboole_0(k4_xboole_0(A_145, A_145), B_146)=k2_xboole_0(B_146, k4_xboole_0(A_145, A_145)))), inference(superposition, [status(thm), theory('equality')], [c_2903, c_1110])).
% 30.33/20.51  tff(c_3088, plain, (![B_146, A_145]: (k2_xboole_0(B_146, k4_xboole_0(A_145, A_145))=B_146)), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2939])).
% 30.33/20.51  tff(c_13277, plain, (![A_282, A_280, B_281]: (k4_xboole_0(A_282, A_282)=k4_xboole_0(A_280, k2_xboole_0(B_281, A_280)))), inference(superposition, [status(thm), theory('equality')], [c_11340, c_3088])).
% 30.33/20.51  tff(c_20520, plain, (![A_332]: (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k4_xboole_0(A_332, A_332))), inference(superposition, [status(thm), theory('equality')], [c_1108, c_13277])).
% 30.33/20.51  tff(c_24, plain, (![A_23, B_24]: (k6_subset_1(A_23, B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.33/20.51  tff(c_26, plain, (![C_27, A_25, B_26]: (k6_subset_1(k10_relat_1(C_27, A_25), k10_relat_1(C_27, B_26))=k10_relat_1(C_27, k6_subset_1(A_25, B_26)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.33/20.51  tff(c_39, plain, (![C_27, A_25, B_26]: (k4_xboole_0(k10_relat_1(C_27, A_25), k10_relat_1(C_27, B_26))=k10_relat_1(C_27, k4_xboole_0(A_25, B_26)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 30.33/20.51  tff(c_20720, plain, (![A_332]: (k4_xboole_0(A_332, A_332)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20520, c_39])).
% 30.33/20.51  tff(c_22351, plain, (![A_344]: (k4_xboole_0(A_344, A_344)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_20720])).
% 30.33/20.51  tff(c_190, plain, (![A_48]: (r1_tarski(A_48, k2_relat_1('#skF_3')) | ~r1_tarski(A_48, '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_176])).
% 30.33/20.51  tff(c_1508, plain, (![B_113, A_114]: (k9_relat_1(B_113, k10_relat_1(B_113, A_114))=A_114 | ~r1_tarski(A_114, k2_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.33/20.51  tff(c_1521, plain, (![A_48]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_48))=A_48 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_48, '#skF_1'))), inference(resolution, [status(thm)], [c_190, c_1508])).
% 30.33/20.51  tff(c_1538, plain, (![A_48]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_48))=A_48 | ~r1_tarski(A_48, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1521])).
% 30.33/20.51  tff(c_22391, plain, (![A_344]: (k9_relat_1('#skF_3', k4_xboole_0(A_344, A_344))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22351, c_1538])).
% 30.33/20.51  tff(c_22665, plain, (![A_344]: (k9_relat_1('#skF_3', k4_xboole_0(A_344, A_344))=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22391])).
% 30.33/20.51  tff(c_3161, plain, (![B_149, A_150]: (k2_xboole_0(B_149, k4_xboole_0(A_150, A_150))=B_149)), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2939])).
% 30.33/20.51  tff(c_3296, plain, (![A_18, A_150]: (k4_xboole_0(A_18, A_18)=k4_xboole_0(A_150, A_150))), inference(superposition, [status(thm), theory('equality')], [c_2901, c_3161])).
% 30.33/20.51  tff(c_1109, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_12, c_1036])).
% 30.33/20.51  tff(c_5836, plain, (![A_186, B_187]: (k4_xboole_0(k4_xboole_0(A_186, A_186), B_187)=k4_xboole_0(A_186, A_186))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_2903])).
% 30.33/20.51  tff(c_5980, plain, (![A_150, B_187, A_18]: (k4_xboole_0(k4_xboole_0(A_150, A_150), B_187)=k4_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_3296, c_5836])).
% 30.33/20.51  tff(c_300, plain, (![A_56, B_57, B_9]: (r1_tarski(k4_xboole_0(A_56, B_57), k2_xboole_0(B_9, A_56)))), inference(resolution, [status(thm)], [c_238, c_277])).
% 30.33/20.51  tff(c_3390, plain, (![B_151]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), B_151), k10_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1108, c_300])).
% 30.33/20.51  tff(c_3407, plain, (![B_26]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_26)), k10_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_3390])).
% 30.33/20.51  tff(c_36719, plain, (![B_441]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_441)), k10_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3407])).
% 30.33/20.51  tff(c_36784, plain, (![A_18]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_18, A_18)), k10_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3296, c_36719])).
% 30.33/20.51  tff(c_189, plain, (![A_48, A_18, B_19]: (r1_tarski(A_48, k2_xboole_0(A_18, B_19)) | ~r1_tarski(A_48, A_18))), inference(resolution, [status(thm)], [c_20, c_176])).
% 30.33/20.51  tff(c_1915, plain, (![C_127, A_128, B_129]: (k4_xboole_0(k10_relat_1(C_127, A_128), k10_relat_1(C_127, B_129))=k10_relat_1(C_127, k4_xboole_0(A_128, B_129)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 30.33/20.51  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 30.33/20.51  tff(c_14573, plain, (![C_290, A_291, B_292, C_293]: (r1_tarski(k10_relat_1(C_290, k4_xboole_0(A_291, B_292)), C_293) | ~r1_tarski(k10_relat_1(C_290, A_291), k2_xboole_0(k10_relat_1(C_290, B_292), C_293)) | ~v1_funct_1(C_290) | ~v1_relat_1(C_290))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_14])).
% 30.33/20.51  tff(c_133881, plain, (![C_913, A_914, B_915, B_916]: (r1_tarski(k10_relat_1(C_913, k4_xboole_0(A_914, B_915)), B_916) | ~v1_funct_1(C_913) | ~v1_relat_1(C_913) | ~r1_tarski(k10_relat_1(C_913, A_914), k10_relat_1(C_913, B_915)))), inference(resolution, [status(thm)], [c_189, c_14573])).
% 30.33/20.51  tff(c_133885, plain, (![A_18, B_916]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0(A_18, A_18), '#skF_2')), B_916) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_36784, c_133881])).
% 30.33/20.51  tff(c_133936, plain, (![A_917, B_918]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_917, A_917)), B_918))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_5980, c_133885])).
% 30.33/20.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.33/20.51  tff(c_8852, plain, (![A_224, B_225, C_226]: (k4_xboole_0(A_224, B_225)=C_226 | ~r1_tarski(C_226, k4_xboole_0(A_224, B_225)) | ~r1_tarski(A_224, k2_xboole_0(B_225, C_226)))), inference(resolution, [status(thm)], [c_644, c_2])).
% 30.33/20.51  tff(c_8891, plain, (![A_150, C_226, A_18]: (k4_xboole_0(A_150, A_150)=C_226 | ~r1_tarski(C_226, k4_xboole_0(A_18, A_18)) | ~r1_tarski(A_150, k2_xboole_0(A_150, C_226)))), inference(superposition, [status(thm), theory('equality')], [c_3296, c_8852])).
% 30.33/20.51  tff(c_8942, plain, (![A_150, C_226, A_18]: (k4_xboole_0(A_150, A_150)=C_226 | ~r1_tarski(C_226, k4_xboole_0(A_18, A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8891])).
% 30.33/20.51  tff(c_134465, plain, (![A_920, A_921]: (k4_xboole_0(A_920, A_920)=k10_relat_1('#skF_3', k4_xboole_0(A_921, A_921)))), inference(resolution, [status(thm)], [c_133936, c_8942])).
% 30.33/20.51  tff(c_53, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.33/20.51  tff(c_68, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_53])).
% 30.33/20.51  tff(c_12173, plain, (![B_265, A_266, B_267]: (k9_relat_1(B_265, k10_relat_1(B_265, k4_xboole_0(A_266, B_267)))=k4_xboole_0(A_266, B_267) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265) | ~r1_tarski(A_266, k2_xboole_0(B_267, k2_relat_1(B_265))))), inference(resolution, [status(thm)], [c_14, c_1508])).
% 30.33/20.51  tff(c_12297, plain, (![A_266]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k4_xboole_0(A_266, '#skF_1')))=k4_xboole_0(A_266, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_266, k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_12173])).
% 30.33/20.51  tff(c_12348, plain, (![A_266]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k4_xboole_0(A_266, '#skF_1')))=k4_xboole_0(A_266, '#skF_1') | ~r1_tarski(A_266, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_12297])).
% 30.33/20.51  tff(c_134696, plain, (![A_920]: (k9_relat_1('#skF_3', k4_xboole_0(A_920, A_920))=k4_xboole_0('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_134465, c_12348])).
% 30.33/20.51  tff(c_135306, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22665, c_134696])).
% 30.33/20.51  tff(c_306, plain, (![A_67, B_68]: (r1_tarski(A_67, k2_xboole_0(B_68, A_67)))), inference(resolution, [status(thm)], [c_12, c_277])).
% 30.33/20.51  tff(c_339, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k2_xboole_0(B_68, A_67))=k2_xboole_0(B_68, A_67))), inference(resolution, [status(thm)], [c_306, c_8])).
% 30.33/20.51  tff(c_664, plain, (![A_88, B_89, B_90]: (r1_tarski(A_88, k2_xboole_0(B_89, k2_xboole_0(k4_xboole_0(A_88, B_89), B_90))))), inference(resolution, [status(thm)], [c_20, c_277])).
% 30.33/20.51  tff(c_683, plain, (![A_88, A_67]: (r1_tarski(A_88, k2_xboole_0(k4_xboole_0(A_88, A_67), A_67)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_664])).
% 30.33/20.51  tff(c_6392, plain, (![A_193, A_194]: (k2_xboole_0(k4_xboole_0(A_193, k4_xboole_0(A_193, A_194)), A_194)=A_194)), inference(resolution, [status(thm)], [c_683, c_2748])).
% 30.33/20.51  tff(c_6787, plain, (![A_198, A_199]: (r1_tarski(k4_xboole_0(A_198, k4_xboole_0(A_198, A_199)), A_199))), inference(superposition, [status(thm), theory('equality')], [c_6392, c_20])).
% 30.33/20.51  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 30.33/20.51  tff(c_1015, plain, (![B_17, B_103, A_16]: (r1_tarski(B_17, B_103) | ~r1_tarski(k4_xboole_0(B_17, A_16), B_103) | ~r1_tarski(A_16, B_103) | ~r1_tarski(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_974])).
% 30.33/20.51  tff(c_6790, plain, (![A_198, A_199]: (r1_tarski(A_198, A_199) | ~r1_tarski(k4_xboole_0(A_198, A_199), A_199) | ~r1_tarski(k4_xboole_0(A_198, A_199), A_198))), inference(resolution, [status(thm)], [c_6787, c_1015])).
% 30.33/20.51  tff(c_6858, plain, (![A_198, A_199]: (r1_tarski(A_198, A_199) | ~r1_tarski(k4_xboole_0(A_198, A_199), A_199))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6790])).
% 30.33/20.51  tff(c_135947, plain, (r1_tarski('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135306, c_6858])).
% 30.33/20.51  tff(c_136089, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3035, c_135947])).
% 30.33/20.51  tff(c_136091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_136089])).
% 30.33/20.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.33/20.51  
% 30.33/20.51  Inference rules
% 30.33/20.51  ----------------------
% 30.33/20.51  #Ref     : 0
% 30.33/20.51  #Sup     : 32836
% 30.33/20.51  #Fact    : 0
% 30.33/20.51  #Define  : 0
% 30.33/20.51  #Split   : 7
% 30.33/20.51  #Chain   : 0
% 30.33/20.51  #Close   : 0
% 30.33/20.51  
% 30.33/20.51  Ordering : KBO
% 30.33/20.51  
% 30.33/20.51  Simplification rules
% 30.33/20.51  ----------------------
% 30.33/20.51  #Subsume      : 4489
% 30.33/20.51  #Demod        : 23904
% 30.33/20.51  #Tautology    : 16743
% 30.33/20.51  #SimpNegUnit  : 8
% 30.33/20.51  #BackRed      : 52
% 30.33/20.51  
% 30.33/20.51  #Partial instantiations: 0
% 30.33/20.51  #Strategies tried      : 1
% 30.33/20.51  
% 30.33/20.51  Timing (in seconds)
% 30.33/20.51  ----------------------
% 30.33/20.51  Preprocessing        : 0.31
% 30.33/20.51  Parsing              : 0.17
% 30.33/20.51  CNF conversion       : 0.02
% 30.33/20.51  Main loop            : 19.42
% 30.33/20.51  Inferencing          : 1.93
% 30.33/20.51  Reduction            : 11.30
% 30.33/20.51  Demodulation         : 10.27
% 30.33/20.51  BG Simplification    : 0.24
% 30.33/20.51  Subsumption          : 5.14
% 30.33/20.51  Abstraction          : 0.42
% 30.33/20.51  MUC search           : 0.00
% 30.33/20.51  Cooper               : 0.00
% 30.33/20.51  Total                : 19.77
% 30.33/20.51  Index Insertion      : 0.00
% 30.33/20.51  Index Deletion       : 0.00
% 30.33/20.51  Index Matching       : 0.00
% 30.33/20.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
