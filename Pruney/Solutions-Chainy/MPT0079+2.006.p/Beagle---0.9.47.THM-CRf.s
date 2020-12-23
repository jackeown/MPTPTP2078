%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:43 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 549 expanded)
%              Number of leaves         :   27 ( 197 expanded)
%              Depth                    :   23
%              Number of atoms          :  105 ( 644 expanded)
%              Number of equality atoms :   87 ( 497 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_26,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_337,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_886,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(A_67,B_68)
      | k3_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_337])).

tff(c_898,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_886])).

tff(c_942,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_957,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_942])).

tff(c_983,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_957])).

tff(c_1251,plain,(
    ! [A_78,B_79,C_80] : k4_xboole_0(k4_xboole_0(A_78,B_79),C_80) = k4_xboole_0(A_78,k2_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2006,plain,(
    ! [C_96] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_96)) = k4_xboole_0('#skF_6',C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_1251])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_51,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    k2_xboole_0('#skF_6','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_51])).

tff(c_181,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_188,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_181])).

tff(c_2022,plain,(
    k4_xboole_0('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2006,c_188])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2063,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k3_xboole_0('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_22])).

tff(c_2067,plain,(
    k3_xboole_0('#skF_3','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4,c_2063])).

tff(c_194,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_248,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_266,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_248])).

tff(c_279,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_266])).

tff(c_1650,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k2_xboole_0(B_90,k1_xboole_0)) = k4_xboole_0(A_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1251])).

tff(c_1675,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,k2_xboole_0(B_90,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_22])).

tff(c_3248,plain,(
    ! [A_122,B_123] : k3_xboole_0(A_122,k2_xboole_0(B_123,k1_xboole_0)) = k3_xboole_0(A_122,B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1675])).

tff(c_3311,plain,(
    ! [B_123,A_122] : k3_xboole_0(k2_xboole_0(B_123,k1_xboole_0),A_122) = k3_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_3248,c_4])).

tff(c_3451,plain,(
    ! [B_125,A_126] : k3_xboole_0(k2_xboole_0(B_125,k1_xboole_0),A_126) = k3_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_3248,c_4])).

tff(c_2284,plain,(
    ! [A_101,C_102] : k4_xboole_0(A_101,k2_xboole_0(k1_xboole_0,C_102)) = k4_xboole_0(A_101,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1251])).

tff(c_2325,plain,(
    ! [A_101,C_102] : k4_xboole_0(A_101,k4_xboole_0(A_101,C_102)) = k3_xboole_0(A_101,k2_xboole_0(k1_xboole_0,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2284,c_22])).

tff(c_2395,plain,(
    ! [A_101,C_102] : k3_xboole_0(A_101,k2_xboole_0(k1_xboole_0,C_102)) = k3_xboole_0(A_101,C_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2325])).

tff(c_3469,plain,(
    ! [C_102,B_125] : k3_xboole_0(k2_xboole_0(k1_xboole_0,C_102),B_125) = k3_xboole_0(k2_xboole_0(B_125,k1_xboole_0),C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_2395])).

tff(c_4311,plain,(
    ! [C_141,B_142] : k3_xboole_0(k2_xboole_0(k1_xboole_0,C_141),B_142) = k3_xboole_0(C_141,B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3311,c_3469])).

tff(c_275,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_248])).

tff(c_272,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_248])).

tff(c_281,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_272])).

tff(c_966,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_942])).

tff(c_986,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_275,c_966])).

tff(c_1126,plain,(
    ! [A_75] : k4_xboole_0(A_75,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_275])).

tff(c_1131,plain,(
    ! [A_75] : k4_xboole_0(A_75,k1_xboole_0) = k3_xboole_0(A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_22])).

tff(c_1143,plain,(
    ! [A_75] : k3_xboole_0(A_75,A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1131])).

tff(c_4369,plain,(
    ! [C_141] : k3_xboole_0(C_141,k2_xboole_0(k1_xboole_0,C_141)) = k2_xboole_0(k1_xboole_0,C_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_4311,c_1143])).

tff(c_4473,plain,(
    ! [C_141] : k2_xboole_0(k1_xboole_0,C_141) = C_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_4369])).

tff(c_30,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_899,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_886])).

tff(c_930,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_4])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1306,plain,(
    ! [A_18,B_19,C_80] : k4_xboole_0(A_18,k2_xboole_0(k3_xboole_0(A_18,B_19),C_80)) = k4_xboole_0(k4_xboole_0(A_18,B_19),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1251])).

tff(c_4706,plain,(
    ! [A_147,B_148,C_149] : k4_xboole_0(A_147,k2_xboole_0(k3_xboole_0(A_147,B_148),C_149)) = k4_xboole_0(A_147,k2_xboole_0(B_148,C_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1306])).

tff(c_4800,plain,(
    ! [C_149] : k4_xboole_0('#skF_3',k2_xboole_0(k1_xboole_0,C_149)) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_4706])).

tff(c_5539,plain,(
    ! [C_163] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_163)) = k4_xboole_0('#skF_3',C_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_4800])).

tff(c_5583,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_5539])).

tff(c_5594,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_5583])).

tff(c_5610,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5594,c_22])).

tff(c_5617,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_16,c_5610])).

tff(c_5642,plain,(
    k2_xboole_0('#skF_3','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_93])).

tff(c_916,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_898])).

tff(c_4803,plain,(
    ! [C_149] : k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,C_149)) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_4706])).

tff(c_4865,plain,(
    ! [C_149] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_149)) = k4_xboole_0('#skF_4',C_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_4803])).

tff(c_8047,plain,(
    ! [C_194] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_194)) = k4_xboole_0('#skF_4',C_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_4865])).

tff(c_8114,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5642,c_8047])).

tff(c_8158,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_8114])).

tff(c_8187,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8158,c_22])).

tff(c_8197,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8187])).

tff(c_954,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_942])).

tff(c_982,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_954])).

tff(c_1522,plain,(
    ! [C_85] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_3',C_85)) = k4_xboole_0('#skF_5',C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_1251])).

tff(c_11450,plain,(
    ! [B_235] : k4_xboole_0('#skF_5',k2_xboole_0(B_235,'#skF_3')) = k4_xboole_0('#skF_5',B_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1522])).

tff(c_197,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_181])).

tff(c_11522,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11450,c_197])).

tff(c_11647,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11522,c_22])).

tff(c_11661,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8197,c_16,c_4,c_11647])).

tff(c_11663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_11661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.37/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.74  
% 7.37/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.37/2.75  
% 7.37/2.75  %Foreground sorts:
% 7.37/2.75  
% 7.37/2.75  
% 7.37/2.75  %Background operators:
% 7.37/2.75  
% 7.37/2.75  
% 7.37/2.75  %Foreground operators:
% 7.37/2.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.37/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.37/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.37/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.37/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.37/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.37/2.75  tff('#skF_5', type, '#skF_5': $i).
% 7.37/2.75  tff('#skF_6', type, '#skF_6': $i).
% 7.37/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.37/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.37/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.37/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.37/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.37/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.37/2.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.37/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.37/2.75  
% 7.54/2.76  tff(f_74, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 7.54/2.76  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.54/2.76  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.54/2.76  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.54/2.76  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.54/2.76  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.54/2.76  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.54/2.76  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.54/2.76  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.54/2.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.54/2.76  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.54/2.76  tff(c_26, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.76  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.54/2.76  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.54/2.76  tff(c_162, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.54/2.76  tff(c_178, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_162])).
% 7.54/2.76  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.54/2.76  tff(c_28, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.76  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.54/2.76  tff(c_337, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.54/2.76  tff(c_886, plain, (![A_67, B_68]: (~r1_xboole_0(A_67, B_68) | k3_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_337])).
% 7.54/2.76  tff(c_898, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_886])).
% 7.54/2.76  tff(c_942, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.76  tff(c_957, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_898, c_942])).
% 7.54/2.76  tff(c_983, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_957])).
% 7.54/2.76  tff(c_1251, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k4_xboole_0(A_78, B_79), C_80)=k4_xboole_0(A_78, k2_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.54/2.76  tff(c_2006, plain, (![C_96]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_96))=k4_xboole_0('#skF_6', C_96))), inference(superposition, [status(thm), theory('equality')], [c_983, c_1251])).
% 7.54/2.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.54/2.76  tff(c_32, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.76  tff(c_33, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 7.54/2.76  tff(c_51, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.54/2.76  tff(c_93, plain, (k2_xboole_0('#skF_6', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_51])).
% 7.54/2.76  tff(c_181, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_162])).
% 7.54/2.76  tff(c_188, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_181])).
% 7.54/2.76  tff(c_2022, plain, (k4_xboole_0('#skF_6', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2006, c_188])).
% 7.54/2.76  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.54/2.76  tff(c_2063, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k3_xboole_0('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2022, c_22])).
% 7.54/2.76  tff(c_2067, plain, (k3_xboole_0('#skF_3', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4, c_2063])).
% 7.54/2.76  tff(c_194, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 7.54/2.76  tff(c_248, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.54/2.76  tff(c_266, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k4_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_248])).
% 7.54/2.76  tff(c_279, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_266])).
% 7.54/2.76  tff(c_1650, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k2_xboole_0(B_90, k1_xboole_0))=k4_xboole_0(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1251])).
% 7.54/2.76  tff(c_1675, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, k2_xboole_0(B_90, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_22])).
% 7.54/2.76  tff(c_3248, plain, (![A_122, B_123]: (k3_xboole_0(A_122, k2_xboole_0(B_123, k1_xboole_0))=k3_xboole_0(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1675])).
% 7.54/2.76  tff(c_3311, plain, (![B_123, A_122]: (k3_xboole_0(k2_xboole_0(B_123, k1_xboole_0), A_122)=k3_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_3248, c_4])).
% 7.54/2.76  tff(c_3451, plain, (![B_125, A_126]: (k3_xboole_0(k2_xboole_0(B_125, k1_xboole_0), A_126)=k3_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_3248, c_4])).
% 7.54/2.76  tff(c_2284, plain, (![A_101, C_102]: (k4_xboole_0(A_101, k2_xboole_0(k1_xboole_0, C_102))=k4_xboole_0(A_101, C_102))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1251])).
% 7.54/2.76  tff(c_2325, plain, (![A_101, C_102]: (k4_xboole_0(A_101, k4_xboole_0(A_101, C_102))=k3_xboole_0(A_101, k2_xboole_0(k1_xboole_0, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_2284, c_22])).
% 7.54/2.76  tff(c_2395, plain, (![A_101, C_102]: (k3_xboole_0(A_101, k2_xboole_0(k1_xboole_0, C_102))=k3_xboole_0(A_101, C_102))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2325])).
% 7.54/2.76  tff(c_3469, plain, (![C_102, B_125]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, C_102), B_125)=k3_xboole_0(k2_xboole_0(B_125, k1_xboole_0), C_102))), inference(superposition, [status(thm), theory('equality')], [c_3451, c_2395])).
% 7.54/2.76  tff(c_4311, plain, (![C_141, B_142]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, C_141), B_142)=k3_xboole_0(C_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_3311, c_3469])).
% 7.54/2.76  tff(c_275, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_248])).
% 7.54/2.76  tff(c_272, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k4_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_178, c_248])).
% 7.54/2.76  tff(c_281, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_272])).
% 7.54/2.76  tff(c_966, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k4_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_281, c_942])).
% 7.54/2.76  tff(c_986, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_275, c_966])).
% 7.54/2.76  tff(c_1126, plain, (![A_75]: (k4_xboole_0(A_75, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_986, c_275])).
% 7.54/2.76  tff(c_1131, plain, (![A_75]: (k4_xboole_0(A_75, k1_xboole_0)=k3_xboole_0(A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_1126, c_22])).
% 7.54/2.76  tff(c_1143, plain, (![A_75]: (k3_xboole_0(A_75, A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1131])).
% 7.54/2.76  tff(c_4369, plain, (![C_141]: (k3_xboole_0(C_141, k2_xboole_0(k1_xboole_0, C_141))=k2_xboole_0(k1_xboole_0, C_141))), inference(superposition, [status(thm), theory('equality')], [c_4311, c_1143])).
% 7.54/2.76  tff(c_4473, plain, (![C_141]: (k2_xboole_0(k1_xboole_0, C_141)=C_141)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_4369])).
% 7.54/2.76  tff(c_30, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.54/2.76  tff(c_899, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_886])).
% 7.54/2.76  tff(c_930, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_899, c_4])).
% 7.54/2.76  tff(c_18, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.54/2.76  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.76  tff(c_1306, plain, (![A_18, B_19, C_80]: (k4_xboole_0(A_18, k2_xboole_0(k3_xboole_0(A_18, B_19), C_80))=k4_xboole_0(k4_xboole_0(A_18, B_19), C_80))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1251])).
% 7.54/2.76  tff(c_4706, plain, (![A_147, B_148, C_149]: (k4_xboole_0(A_147, k2_xboole_0(k3_xboole_0(A_147, B_148), C_149))=k4_xboole_0(A_147, k2_xboole_0(B_148, C_149)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1306])).
% 7.54/2.76  tff(c_4800, plain, (![C_149]: (k4_xboole_0('#skF_3', k2_xboole_0(k1_xboole_0, C_149))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_149)))), inference(superposition, [status(thm), theory('equality')], [c_930, c_4706])).
% 7.54/2.76  tff(c_5539, plain, (![C_163]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_163))=k4_xboole_0('#skF_3', C_163))), inference(demodulation, [status(thm), theory('equality')], [c_4473, c_4800])).
% 7.54/2.76  tff(c_5583, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_33, c_5539])).
% 7.54/2.76  tff(c_5594, plain, (k4_xboole_0('#skF_3', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_194, c_5583])).
% 7.54/2.76  tff(c_5610, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5594, c_22])).
% 7.54/2.76  tff(c_5617, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2067, c_16, c_5610])).
% 7.54/2.76  tff(c_5642, plain, (k2_xboole_0('#skF_3', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_93])).
% 7.54/2.76  tff(c_916, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4, c_898])).
% 7.54/2.76  tff(c_4803, plain, (![C_149]: (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, C_149))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_149)))), inference(superposition, [status(thm), theory('equality')], [c_916, c_4706])).
% 7.54/2.76  tff(c_4865, plain, (![C_149]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_149))=k4_xboole_0('#skF_4', C_149))), inference(demodulation, [status(thm), theory('equality')], [c_4473, c_4803])).
% 7.54/2.76  tff(c_8047, plain, (![C_194]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_194))=k4_xboole_0('#skF_4', C_194))), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_4865])).
% 7.54/2.76  tff(c_8114, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5642, c_8047])).
% 7.54/2.76  tff(c_8158, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_178, c_8114])).
% 7.54/2.76  tff(c_8187, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8158, c_22])).
% 7.54/2.76  tff(c_8197, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8187])).
% 7.54/2.76  tff(c_954, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_899, c_942])).
% 7.54/2.76  tff(c_982, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_954])).
% 7.54/2.76  tff(c_1522, plain, (![C_85]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_3', C_85))=k4_xboole_0('#skF_5', C_85))), inference(superposition, [status(thm), theory('equality')], [c_982, c_1251])).
% 7.54/2.76  tff(c_11450, plain, (![B_235]: (k4_xboole_0('#skF_5', k2_xboole_0(B_235, '#skF_3'))=k4_xboole_0('#skF_5', B_235))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1522])).
% 7.54/2.76  tff(c_197, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33, c_181])).
% 7.54/2.76  tff(c_11522, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11450, c_197])).
% 7.54/2.76  tff(c_11647, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11522, c_22])).
% 7.54/2.76  tff(c_11661, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8197, c_16, c_4, c_11647])).
% 7.54/2.76  tff(c_11663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_11661])).
% 7.54/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.76  
% 7.54/2.76  Inference rules
% 7.54/2.76  ----------------------
% 7.54/2.76  #Ref     : 0
% 7.54/2.76  #Sup     : 2869
% 7.54/2.76  #Fact    : 0
% 7.54/2.76  #Define  : 0
% 7.54/2.76  #Split   : 9
% 7.54/2.76  #Chain   : 0
% 7.54/2.76  #Close   : 0
% 7.54/2.76  
% 7.54/2.76  Ordering : KBO
% 7.54/2.76  
% 7.54/2.76  Simplification rules
% 7.54/2.76  ----------------------
% 7.54/2.76  #Subsume      : 191
% 7.54/2.76  #Demod        : 3139
% 7.54/2.76  #Tautology    : 1882
% 7.54/2.76  #SimpNegUnit  : 27
% 7.54/2.76  #BackRed      : 38
% 7.54/2.76  
% 7.54/2.76  #Partial instantiations: 0
% 7.54/2.76  #Strategies tried      : 1
% 7.54/2.76  
% 7.54/2.76  Timing (in seconds)
% 7.54/2.76  ----------------------
% 7.54/2.77  Preprocessing        : 0.32
% 7.54/2.77  Parsing              : 0.17
% 7.54/2.77  CNF conversion       : 0.02
% 7.54/2.77  Main loop            : 1.63
% 7.54/2.77  Inferencing          : 0.42
% 7.54/2.77  Reduction            : 0.85
% 7.54/2.77  Demodulation         : 0.73
% 7.54/2.77  BG Simplification    : 0.04
% 7.54/2.77  Subsumption          : 0.21
% 7.54/2.77  Abstraction          : 0.06
% 7.54/2.77  MUC search           : 0.00
% 7.54/2.77  Cooper               : 0.00
% 7.54/2.77  Total                : 1.99
% 7.54/2.77  Index Insertion      : 0.00
% 7.54/2.77  Index Deletion       : 0.00
% 7.54/2.77  Index Matching       : 0.00
% 7.54/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
