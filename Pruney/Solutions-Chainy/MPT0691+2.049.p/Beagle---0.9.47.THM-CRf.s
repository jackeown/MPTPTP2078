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
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 18.23s
% Output     : CNFRefutation 18.36s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 398 expanded)
%              Number of leaves         :   48 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 ( 727 expanded)
%              Number of equality atoms :   61 ( 237 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_80,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_118,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_154,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | k4_xboole_0(A_94,B_95) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_162,plain,(
    k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_68])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_175,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_172])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k7_relat_1(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    ! [A_71,B_72] :
      ( k5_relat_1(k6_relat_1(A_71),B_72) = k7_relat_1(B_72,A_71)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ! [A_50] : v1_relat_1(k6_relat_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2214,plain,(
    ! [C_225,A_226,B_227] :
      ( r1_tarski(C_225,'#skF_1'(A_226,B_227,C_225))
      | k2_xboole_0(A_226,C_225) = B_227
      | ~ r1_tarski(C_225,B_227)
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [B_13,A_12,C_14] :
      ( ~ r1_tarski(B_13,'#skF_1'(A_12,B_13,C_14))
      | k2_xboole_0(A_12,C_14) = B_13
      | ~ r1_tarski(C_14,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2218,plain,(
    ! [A_226,B_227] :
      ( k2_xboole_0(A_226,B_227) = B_227
      | ~ r1_tarski(B_227,B_227)
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_2214,c_18])).

tff(c_2242,plain,(
    ! [A_228,B_229] :
      ( k2_xboole_0(A_228,B_229) = B_229
      | ~ r1_tarski(A_228,B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2218])).

tff(c_2297,plain,(
    k2_xboole_0('#skF_2',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2242])).

tff(c_58,plain,(
    ! [A_68] : k1_relat_1(k6_relat_1(A_68)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_233,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k10_relat_1(B_107,A_108),k1_relat_1(B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_239,plain,(
    ! [A_68,A_108] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_68),A_108),A_68)
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_233])).

tff(c_242,plain,(
    ! [A_68,A_108] : r1_tarski(k10_relat_1(k6_relat_1(A_68),A_108),A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_239])).

tff(c_489,plain,(
    ! [A_146,C_147,B_148] :
      ( r1_tarski(k2_xboole_0(A_146,C_147),B_148)
      | ~ r1_tarski(C_147,B_148)
      | ~ r1_tarski(A_146,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_307,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_326,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(k2_xboole_0(A_16,B_17),A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_307])).

tff(c_496,plain,(
    ! [B_148,C_147] :
      ( k2_xboole_0(B_148,C_147) = B_148
      | ~ r1_tarski(C_147,B_148)
      | ~ r1_tarski(B_148,B_148) ) ),
    inference(resolution,[status(thm)],[c_489,c_326])).

tff(c_512,plain,(
    ! [B_149,C_150] :
      ( k2_xboole_0(B_149,C_150) = B_149
      | ~ r1_tarski(C_150,B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_496])).

tff(c_546,plain,(
    ! [A_68,A_108] : k2_xboole_0(A_68,k10_relat_1(k6_relat_1(A_68),A_108)) = A_68 ),
    inference(resolution,[status(thm)],[c_242,c_512])).

tff(c_60,plain,(
    ! [A_68] : k2_relat_1(k6_relat_1(A_68)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_243,plain,(
    ! [A_109] :
      ( k10_relat_1(A_109,k2_relat_1(A_109)) = k1_relat_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_255,plain,(
    ! [A_68] :
      ( k10_relat_1(k6_relat_1(A_68),A_68) = k1_relat_1(k6_relat_1(A_68))
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_243])).

tff(c_260,plain,(
    ! [A_68] : k10_relat_1(k6_relat_1(A_68),A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_58,c_255])).

tff(c_1285,plain,(
    ! [C_187,A_188,B_189] :
      ( k2_xboole_0(k10_relat_1(C_187,A_188),k10_relat_1(C_187,B_189)) = k10_relat_1(C_187,k2_xboole_0(A_188,B_189))
      | ~ v1_relat_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1347,plain,(
    ! [A_68,B_189] :
      ( k2_xboole_0(A_68,k10_relat_1(k6_relat_1(A_68),B_189)) = k10_relat_1(k6_relat_1(A_68),k2_xboole_0(A_68,B_189))
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_1285])).

tff(c_1362,plain,(
    ! [A_68,B_189] : k10_relat_1(k6_relat_1(A_68),k2_xboole_0(A_68,B_189)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_546,c_1347])).

tff(c_2315,plain,(
    k10_relat_1(k6_relat_1('#skF_2'),k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_1362])).

tff(c_56,plain,(
    ! [A_65,B_67] :
      ( k10_relat_1(A_65,k1_relat_1(B_67)) = k1_relat_1(k5_relat_1(A_65,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2424,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3')) = '#skF_2'
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_56])).

tff(c_2459,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72,c_2424])).

tff(c_2506,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2459])).

tff(c_2519,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2506])).

tff(c_50,plain,(
    ! [B_60,A_59] :
      ( r1_tarski(k10_relat_1(B_60,A_59),k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2547,plain,(
    ! [A_59] :
      ( r1_tarski(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_59),'#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_50])).

tff(c_58739,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2547])).

tff(c_58742,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_58739])).

tff(c_58746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58742])).

tff(c_58748,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2547])).

tff(c_62,plain,(
    ! [B_70,A_69] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_70,A_69)),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1033,plain,(
    ! [A_169,C_170,B_171] :
      ( k9_relat_1(k7_relat_1(A_169,C_170),B_171) = k9_relat_1(A_169,B_171)
      | ~ r1_tarski(B_171,C_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_53] :
      ( k9_relat_1(A_53,k1_relat_1(A_53)) = k2_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_29406,plain,(
    ! [A_586,C_587] :
      ( k9_relat_1(A_586,k1_relat_1(k7_relat_1(A_586,C_587))) = k2_relat_1(k7_relat_1(A_586,C_587))
      | ~ v1_relat_1(k7_relat_1(A_586,C_587))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_586,C_587)),C_587)
      | ~ v1_relat_1(A_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_46])).

tff(c_77249,plain,(
    ! [B_907,A_908] :
      ( k9_relat_1(B_907,k1_relat_1(k7_relat_1(B_907,A_908))) = k2_relat_1(k7_relat_1(B_907,A_908))
      | ~ v1_relat_1(k7_relat_1(B_907,A_908))
      | ~ v1_relat_1(B_907) ) ),
    inference(resolution,[status(thm)],[c_62,c_29406])).

tff(c_77277,plain,
    ( k2_relat_1(k7_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_77249])).

tff(c_77296,plain,(
    k2_relat_1(k7_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58748,c_77277])).

tff(c_52,plain,(
    ! [A_61] :
      ( k10_relat_1(A_61,k2_relat_1(A_61)) = k1_relat_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77332,plain,
    ( k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2')) = k1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_77296,c_52])).

tff(c_77356,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58748,c_2519,c_77332])).

tff(c_654,plain,(
    ! [A_152,C_153,B_154] :
      ( k3_xboole_0(A_152,k10_relat_1(C_153,B_154)) = k10_relat_1(k7_relat_1(C_153,A_152),B_154)
      | ~ v1_relat_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_660,plain,(
    ! [A_152,C_153,B_154] :
      ( k5_xboole_0(A_152,k10_relat_1(k7_relat_1(C_153,A_152),B_154)) = k4_xboole_0(A_152,k10_relat_1(C_153,B_154))
      | ~ v1_relat_1(C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_14])).

tff(c_77790,plain,
    ( k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k5_xboole_0('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77356,c_660])).

tff(c_77863,plain,(
    k4_xboole_0('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_175,c_77790])).

tff(c_77865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_77863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.23/10.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.23/10.66  
% 18.23/10.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.23/10.66  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 18.23/10.66  
% 18.23/10.66  %Foreground sorts:
% 18.23/10.66  
% 18.23/10.66  
% 18.23/10.66  %Background operators:
% 18.23/10.66  
% 18.23/10.66  
% 18.23/10.66  %Foreground operators:
% 18.23/10.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.23/10.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.23/10.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.23/10.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.23/10.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.23/10.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.23/10.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.23/10.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.23/10.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.23/10.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.23/10.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.23/10.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.23/10.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.23/10.66  tff('#skF_2', type, '#skF_2': $i).
% 18.23/10.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.23/10.66  tff('#skF_3', type, '#skF_3': $i).
% 18.23/10.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.23/10.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.23/10.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.23/10.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.23/10.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.23/10.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.23/10.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.23/10.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.23/10.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.23/10.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.23/10.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.23/10.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.23/10.66  
% 18.36/10.68  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 18.36/10.68  tff(f_137, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 18.36/10.68  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.36/10.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 18.36/10.68  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 18.36/10.68  tff(f_84, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 18.36/10.68  tff(f_126, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 18.36/10.68  tff(f_80, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 18.36/10.68  tff(f_56, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 18.36/10.68  tff(f_118, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 18.36/10.68  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 18.36/10.68  tff(f_64, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 18.36/10.68  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.36/10.68  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 18.36/10.68  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 18.36/10.68  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 18.36/10.68  tff(f_122, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 18.36/10.68  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 18.36/10.68  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 18.36/10.68  tff(f_130, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 18.36/10.68  tff(c_154, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | k4_xboole_0(A_94, B_95)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.36/10.68  tff(c_68, plain, (~r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.36/10.68  tff(c_162, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_68])).
% 18.36/10.68  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.36/10.68  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.36/10.68  tff(c_114, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.36/10.68  tff(c_126, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_114])).
% 18.36/10.68  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.36/10.68  tff(c_163, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.68  tff(c_172, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_163])).
% 18.36/10.68  tff(c_175, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_172])).
% 18.36/10.68  tff(c_44, plain, (![A_51, B_52]: (v1_relat_1(k7_relat_1(A_51, B_52)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.36/10.68  tff(c_64, plain, (![A_71, B_72]: (k5_relat_1(k6_relat_1(A_71), B_72)=k7_relat_1(B_72, A_71) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_126])).
% 18.36/10.68  tff(c_42, plain, (![A_50]: (v1_relat_1(k6_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.36/10.68  tff(c_70, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.36/10.68  tff(c_2214, plain, (![C_225, A_226, B_227]: (r1_tarski(C_225, '#skF_1'(A_226, B_227, C_225)) | k2_xboole_0(A_226, C_225)=B_227 | ~r1_tarski(C_225, B_227) | ~r1_tarski(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.36/10.68  tff(c_18, plain, (![B_13, A_12, C_14]: (~r1_tarski(B_13, '#skF_1'(A_12, B_13, C_14)) | k2_xboole_0(A_12, C_14)=B_13 | ~r1_tarski(C_14, B_13) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.36/10.68  tff(c_2218, plain, (![A_226, B_227]: (k2_xboole_0(A_226, B_227)=B_227 | ~r1_tarski(B_227, B_227) | ~r1_tarski(A_226, B_227))), inference(resolution, [status(thm)], [c_2214, c_18])).
% 18.36/10.68  tff(c_2242, plain, (![A_228, B_229]: (k2_xboole_0(A_228, B_229)=B_229 | ~r1_tarski(A_228, B_229))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2218])).
% 18.36/10.68  tff(c_2297, plain, (k2_xboole_0('#skF_2', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2242])).
% 18.36/10.68  tff(c_58, plain, (![A_68]: (k1_relat_1(k6_relat_1(A_68))=A_68)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.36/10.68  tff(c_233, plain, (![B_107, A_108]: (r1_tarski(k10_relat_1(B_107, A_108), k1_relat_1(B_107)) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.36/10.68  tff(c_239, plain, (![A_68, A_108]: (r1_tarski(k10_relat_1(k6_relat_1(A_68), A_108), A_68) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_233])).
% 18.36/10.68  tff(c_242, plain, (![A_68, A_108]: (r1_tarski(k10_relat_1(k6_relat_1(A_68), A_108), A_68))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_239])).
% 18.36/10.68  tff(c_489, plain, (![A_146, C_147, B_148]: (r1_tarski(k2_xboole_0(A_146, C_147), B_148) | ~r1_tarski(C_147, B_148) | ~r1_tarski(A_146, B_148))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.36/10.68  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.36/10.68  tff(c_307, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.36/10.68  tff(c_326, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(k2_xboole_0(A_16, B_17), A_16))), inference(resolution, [status(thm)], [c_24, c_307])).
% 18.36/10.68  tff(c_496, plain, (![B_148, C_147]: (k2_xboole_0(B_148, C_147)=B_148 | ~r1_tarski(C_147, B_148) | ~r1_tarski(B_148, B_148))), inference(resolution, [status(thm)], [c_489, c_326])).
% 18.36/10.68  tff(c_512, plain, (![B_149, C_150]: (k2_xboole_0(B_149, C_150)=B_149 | ~r1_tarski(C_150, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_496])).
% 18.36/10.68  tff(c_546, plain, (![A_68, A_108]: (k2_xboole_0(A_68, k10_relat_1(k6_relat_1(A_68), A_108))=A_68)), inference(resolution, [status(thm)], [c_242, c_512])).
% 18.36/10.68  tff(c_60, plain, (![A_68]: (k2_relat_1(k6_relat_1(A_68))=A_68)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.36/10.68  tff(c_243, plain, (![A_109]: (k10_relat_1(A_109, k2_relat_1(A_109))=k1_relat_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.36/10.68  tff(c_255, plain, (![A_68]: (k10_relat_1(k6_relat_1(A_68), A_68)=k1_relat_1(k6_relat_1(A_68)) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_243])).
% 18.36/10.68  tff(c_260, plain, (![A_68]: (k10_relat_1(k6_relat_1(A_68), A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_58, c_255])).
% 18.36/10.68  tff(c_1285, plain, (![C_187, A_188, B_189]: (k2_xboole_0(k10_relat_1(C_187, A_188), k10_relat_1(C_187, B_189))=k10_relat_1(C_187, k2_xboole_0(A_188, B_189)) | ~v1_relat_1(C_187))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/10.68  tff(c_1347, plain, (![A_68, B_189]: (k2_xboole_0(A_68, k10_relat_1(k6_relat_1(A_68), B_189))=k10_relat_1(k6_relat_1(A_68), k2_xboole_0(A_68, B_189)) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_1285])).
% 18.36/10.68  tff(c_1362, plain, (![A_68, B_189]: (k10_relat_1(k6_relat_1(A_68), k2_xboole_0(A_68, B_189))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_546, c_1347])).
% 18.36/10.68  tff(c_2315, plain, (k10_relat_1(k6_relat_1('#skF_2'), k1_relat_1('#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2297, c_1362])).
% 18.36/10.68  tff(c_56, plain, (![A_65, B_67]: (k10_relat_1(A_65, k1_relat_1(B_67))=k1_relat_1(k5_relat_1(A_65, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.36/10.68  tff(c_2424, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'))='#skF_2' | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2315, c_56])).
% 18.36/10.68  tff(c_2459, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72, c_2424])).
% 18.36/10.68  tff(c_2506, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_2459])).
% 18.36/10.68  tff(c_2519, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2506])).
% 18.36/10.68  tff(c_50, plain, (![B_60, A_59]: (r1_tarski(k10_relat_1(B_60, A_59), k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.36/10.68  tff(c_2547, plain, (![A_59]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_59), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2519, c_50])).
% 18.36/10.68  tff(c_58739, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2547])).
% 18.36/10.68  tff(c_58742, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_58739])).
% 18.36/10.68  tff(c_58746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_58742])).
% 18.36/10.68  tff(c_58748, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2547])).
% 18.36/10.68  tff(c_62, plain, (![B_70, A_69]: (r1_tarski(k1_relat_1(k7_relat_1(B_70, A_69)), A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_122])).
% 18.36/10.68  tff(c_1033, plain, (![A_169, C_170, B_171]: (k9_relat_1(k7_relat_1(A_169, C_170), B_171)=k9_relat_1(A_169, B_171) | ~r1_tarski(B_171, C_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.36/10.68  tff(c_46, plain, (![A_53]: (k9_relat_1(A_53, k1_relat_1(A_53))=k2_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.36/10.68  tff(c_29406, plain, (![A_586, C_587]: (k9_relat_1(A_586, k1_relat_1(k7_relat_1(A_586, C_587)))=k2_relat_1(k7_relat_1(A_586, C_587)) | ~v1_relat_1(k7_relat_1(A_586, C_587)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_586, C_587)), C_587) | ~v1_relat_1(A_586))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_46])).
% 18.36/10.68  tff(c_77249, plain, (![B_907, A_908]: (k9_relat_1(B_907, k1_relat_1(k7_relat_1(B_907, A_908)))=k2_relat_1(k7_relat_1(B_907, A_908)) | ~v1_relat_1(k7_relat_1(B_907, A_908)) | ~v1_relat_1(B_907))), inference(resolution, [status(thm)], [c_62, c_29406])).
% 18.36/10.68  tff(c_77277, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_77249])).
% 18.36/10.68  tff(c_77296, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_58748, c_77277])).
% 18.36/10.68  tff(c_52, plain, (![A_61]: (k10_relat_1(A_61, k2_relat_1(A_61))=k1_relat_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.36/10.68  tff(c_77332, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77296, c_52])).
% 18.36/10.68  tff(c_77356, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58748, c_2519, c_77332])).
% 18.36/10.68  tff(c_654, plain, (![A_152, C_153, B_154]: (k3_xboole_0(A_152, k10_relat_1(C_153, B_154))=k10_relat_1(k7_relat_1(C_153, A_152), B_154) | ~v1_relat_1(C_153))), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.36/10.68  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.68  tff(c_660, plain, (![A_152, C_153, B_154]: (k5_xboole_0(A_152, k10_relat_1(k7_relat_1(C_153, A_152), B_154))=k4_xboole_0(A_152, k10_relat_1(C_153, B_154)) | ~v1_relat_1(C_153))), inference(superposition, [status(thm), theory('equality')], [c_654, c_14])).
% 18.36/10.68  tff(c_77790, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k5_xboole_0('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77356, c_660])).
% 18.36/10.68  tff(c_77863, plain, (k4_xboole_0('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_175, c_77790])).
% 18.36/10.68  tff(c_77865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_77863])).
% 18.36/10.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.36/10.68  
% 18.36/10.68  Inference rules
% 18.36/10.68  ----------------------
% 18.36/10.68  #Ref     : 0
% 18.36/10.68  #Sup     : 18624
% 18.36/10.68  #Fact    : 0
% 18.36/10.68  #Define  : 0
% 18.36/10.68  #Split   : 3
% 18.36/10.68  #Chain   : 0
% 18.36/10.68  #Close   : 0
% 18.36/10.68  
% 18.36/10.68  Ordering : KBO
% 18.36/10.68  
% 18.36/10.68  Simplification rules
% 18.36/10.68  ----------------------
% 18.36/10.68  #Subsume      : 3456
% 18.36/10.68  #Demod        : 15023
% 18.36/10.68  #Tautology    : 8951
% 18.36/10.68  #SimpNegUnit  : 1
% 18.36/10.68  #BackRed      : 0
% 18.36/10.68  
% 18.36/10.68  #Partial instantiations: 0
% 18.36/10.68  #Strategies tried      : 1
% 18.36/10.68  
% 18.36/10.68  Timing (in seconds)
% 18.36/10.68  ----------------------
% 18.36/10.68  Preprocessing        : 0.35
% 18.36/10.68  Parsing              : 0.18
% 18.36/10.68  CNF conversion       : 0.02
% 18.36/10.68  Main loop            : 9.57
% 18.36/10.68  Inferencing          : 1.56
% 18.44/10.68  Reduction            : 4.89
% 18.44/10.68  Demodulation         : 4.25
% 18.44/10.68  BG Simplification    : 0.18
% 18.44/10.68  Subsumption          : 2.51
% 18.44/10.68  Abstraction          : 0.29
% 18.44/10.68  MUC search           : 0.00
% 18.44/10.68  Cooper               : 0.00
% 18.44/10.68  Total                : 9.96
% 18.44/10.68  Index Insertion      : 0.00
% 18.44/10.68  Index Deletion       : 0.00
% 18.44/10.68  Index Matching       : 0.00
% 18.44/10.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
