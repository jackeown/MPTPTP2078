%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 676 expanded)
%              Number of leaves         :   41 ( 244 expanded)
%              Depth                    :   16
%              Number of atoms          :  114 ( 837 expanded)
%              Number of equality atoms :   72 ( 544 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_96,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_64,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_731,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5058,plain,(
    ! [B_241,A_242] : k5_xboole_0(k5_xboole_0(B_241,A_242),k3_xboole_0(A_242,B_241)) = k2_xboole_0(B_241,A_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_731])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30] : k5_xboole_0(k5_xboole_0(A_28,B_29),C_30) = k5_xboole_0(A_28,k5_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5088,plain,(
    ! [B_241,A_242] : k5_xboole_0(B_241,k5_xboole_0(A_242,k3_xboole_0(A_242,B_241))) = k2_xboole_0(B_241,A_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_5058,c_42])).

tff(c_5210,plain,(
    ! [B_241,A_242] : k5_xboole_0(B_241,k4_xboole_0(A_242,B_241)) = k2_xboole_0(B_241,A_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5088])).

tff(c_36,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [A_47] : r1_tarski(A_47,k1_zfmisc_1(k3_tarski(A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_242,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_257,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_zfmisc_1(k3_tarski(A_47))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_242])).

tff(c_135,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    ! [A_47] : k3_xboole_0(A_47,k1_zfmisc_1(k3_tarski(A_47))) = A_47 ),
    inference(resolution,[status(thm)],[c_60,c_135])).

tff(c_366,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_375,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_zfmisc_1(k3_tarski(A_47))) = k5_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_366])).

tff(c_387,plain,(
    ! [A_47] : k5_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_375])).

tff(c_871,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k5_xboole_0(A_116,B_117),C_118) = k5_xboole_0(A_116,k5_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_915,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k5_xboole_0(B_117,k5_xboole_0(A_116,B_117))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_871])).

tff(c_20,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_258,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_242])).

tff(c_32,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_486,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k4_xboole_0(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_513,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_486])).

tff(c_518,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_513])).

tff(c_770,plain,(
    ! [A_24] : k5_xboole_0(A_24,k3_xboole_0(A_24,k1_xboole_0)) = k2_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_731])).

tff(c_778,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_518,c_770])).

tff(c_407,plain,(
    ! [A_93,B_94] : k2_xboole_0(A_93,k4_xboole_0(B_94,A_93)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_419,plain,(
    ! [B_12] : k2_xboole_0(B_12,k1_xboole_0) = k2_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_407])).

tff(c_781,plain,(
    ! [B_12] : k2_xboole_0(B_12,B_12) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_419])).

tff(c_147,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_761,plain,(
    ! [B_12] : k5_xboole_0(k5_xboole_0(B_12,B_12),B_12) = k2_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_731])).

tff(c_777,plain,(
    ! [B_12] : k5_xboole_0(k1_xboole_0,B_12) = k2_xboole_0(B_12,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_761])).

tff(c_955,plain,(
    ! [B_12] : k5_xboole_0(k1_xboole_0,B_12) = B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_777])).

tff(c_911,plain,(
    ! [A_47,C_118] : k5_xboole_0(A_47,k5_xboole_0(A_47,C_118)) = k5_xboole_0(k1_xboole_0,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_871])).

tff(c_2556,plain,(
    ! [A_190,C_191] : k5_xboole_0(A_190,k5_xboole_0(A_190,C_191)) = C_191 ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_911])).

tff(c_2596,plain,(
    ! [B_117,A_116] : k5_xboole_0(B_117,k5_xboole_0(A_116,B_117)) = k5_xboole_0(A_116,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_2556])).

tff(c_2649,plain,(
    ! [B_192,A_193] : k5_xboole_0(B_192,k5_xboole_0(A_193,B_192)) = A_193 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2596])).

tff(c_2555,plain,(
    ! [A_47,C_118] : k5_xboole_0(A_47,k5_xboole_0(A_47,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_911])).

tff(c_2658,plain,(
    ! [B_192,A_193] : k5_xboole_0(B_192,A_193) = k5_xboole_0(A_193,B_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_2555])).

tff(c_228,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tarski(A_71),B_72)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_236,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(k1_tarski(A_71),B_72) = k1_tarski(A_71)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_228,c_28])).

tff(c_384,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_366])).

tff(c_3225,plain,(
    ! [B_205,A_206] : k5_xboole_0(B_205,k4_xboole_0(B_205,A_206)) = k3_xboole_0(A_206,B_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_2556])).

tff(c_2640,plain,(
    ! [B_117,A_116] : k5_xboole_0(B_117,k5_xboole_0(A_116,B_117)) = A_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2596])).

tff(c_6318,plain,(
    ! [B_258,A_259] : k5_xboole_0(k4_xboole_0(B_258,A_259),k3_xboole_0(A_259,B_258)) = B_258 ),
    inference(superposition,[status(thm),theory(equality)],[c_3225,c_2640])).

tff(c_6392,plain,(
    ! [B_72,A_71] :
      ( k5_xboole_0(k4_xboole_0(B_72,k1_tarski(A_71)),k1_tarski(A_71)) = B_72
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_6318])).

tff(c_6467,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(k1_tarski(A_71),B_72) = B_72
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5210,c_2658,c_6392])).

tff(c_40,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1076,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_1'(A_127,B_128),B_128)
      | r2_hidden('#skF_2'(A_127,B_128),A_127)
      | B_128 = A_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_324,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,k3_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_337,plain,(
    ! [B_85,C_86] :
      ( ~ r1_xboole_0(B_85,B_85)
      | ~ r2_hidden(C_86,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_324])).

tff(c_345,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_337])).

tff(c_1206,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_138),B_138)
      | k1_xboole_0 = B_138 ) ),
    inference(resolution,[status(thm)],[c_1076,c_345])).

tff(c_14,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1222,plain,(
    ! [A_139,B_140] :
      ( ~ r1_xboole_0(A_139,B_140)
      | k3_xboole_0(A_139,B_140) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1206,c_14])).

tff(c_1249,plain,(
    ! [A_141,B_142] : k3_xboole_0(k4_xboole_0(A_141,B_142),B_142) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1222])).

tff(c_1275,plain,(
    ! [B_142,A_141] : k3_xboole_0(B_142,k4_xboole_0(A_141,B_142)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_2])).

tff(c_5241,plain,(
    ! [B_243,A_244] : k5_xboole_0(B_243,k4_xboole_0(A_244,B_243)) = k2_xboole_0(B_243,A_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5088])).

tff(c_5545,plain,(
    ! [B_248,A_249] : k5_xboole_0(B_248,k2_xboole_0(B_248,A_249)) = k4_xboole_0(A_249,B_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_5241,c_2555])).

tff(c_5996,plain,(
    ! [B_254,A_255] : k5_xboole_0(k2_xboole_0(B_254,A_255),k4_xboole_0(A_255,B_254)) = B_254 ),
    inference(superposition,[status(thm),theory(equality)],[c_5545,c_2640])).

tff(c_8284,plain,(
    ! [A_282,B_283] : k5_xboole_0(k4_xboole_0(A_282,B_283),B_283) = k2_xboole_0(B_283,A_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_5996,c_2640])).

tff(c_767,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_731])).

tff(c_8294,plain,(
    ! [B_283,A_282] : k5_xboole_0(k2_xboole_0(B_283,A_282),k3_xboole_0(B_283,k4_xboole_0(A_282,B_283))) = k2_xboole_0(k4_xboole_0(A_282,B_283),B_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_8284,c_767])).

tff(c_8400,plain,(
    ! [A_282,B_283] : k2_xboole_0(k4_xboole_0(A_282,B_283),B_283) = k2_xboole_0(B_283,A_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1275,c_8294])).

tff(c_62,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9208,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8400,c_62])).

tff(c_9331,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6467,c_9208])).

tff(c_9335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_9331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.39  
% 6.04/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 6.04/2.40  
% 6.04/2.40  %Foreground sorts:
% 6.04/2.40  
% 6.04/2.40  
% 6.04/2.40  %Background operators:
% 6.04/2.40  
% 6.04/2.40  
% 6.04/2.40  %Foreground operators:
% 6.04/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.04/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.04/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.04/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.04/2.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.04/2.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.04/2.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.04/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.04/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.04/2.40  tff('#skF_5', type, '#skF_5': $i).
% 6.04/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.04/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.04/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.04/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.04/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.04/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.04/2.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.04/2.40  
% 6.04/2.42  tff(f_101, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.04/2.42  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.04/2.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.04/2.42  tff(f_80, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.04/2.42  tff(f_78, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.04/2.42  tff(f_72, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.04/2.42  tff(f_96, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 6.04/2.42  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.04/2.42  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.04/2.42  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.04/2.42  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.04/2.42  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.04/2.42  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.04/2.42  tff(f_92, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.04/2.42  tff(f_76, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.04/2.42  tff(f_34, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.04/2.42  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.04/2.42  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.04/2.42  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.04/2.42  tff(c_26, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.04/2.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.04/2.42  tff(c_731, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.04/2.42  tff(c_5058, plain, (![B_241, A_242]: (k5_xboole_0(k5_xboole_0(B_241, A_242), k3_xboole_0(A_242, B_241))=k2_xboole_0(B_241, A_242))), inference(superposition, [status(thm), theory('equality')], [c_2, c_731])).
% 6.04/2.42  tff(c_42, plain, (![A_28, B_29, C_30]: (k5_xboole_0(k5_xboole_0(A_28, B_29), C_30)=k5_xboole_0(A_28, k5_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.04/2.42  tff(c_5088, plain, (![B_241, A_242]: (k5_xboole_0(B_241, k5_xboole_0(A_242, k3_xboole_0(A_242, B_241)))=k2_xboole_0(B_241, A_242))), inference(superposition, [status(thm), theory('equality')], [c_5058, c_42])).
% 6.04/2.42  tff(c_5210, plain, (![B_241, A_242]: (k5_xboole_0(B_241, k4_xboole_0(A_242, B_241))=k2_xboole_0(B_241, A_242))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5088])).
% 6.04/2.42  tff(c_36, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.04/2.42  tff(c_60, plain, (![A_47]: (r1_tarski(A_47, k1_zfmisc_1(k3_tarski(A_47))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.04/2.42  tff(c_242, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.04/2.42  tff(c_257, plain, (![A_47]: (k4_xboole_0(A_47, k1_zfmisc_1(k3_tarski(A_47)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_242])).
% 6.04/2.42  tff(c_135, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.04/2.42  tff(c_146, plain, (![A_47]: (k3_xboole_0(A_47, k1_zfmisc_1(k3_tarski(A_47)))=A_47)), inference(resolution, [status(thm)], [c_60, c_135])).
% 6.04/2.42  tff(c_366, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.04/2.42  tff(c_375, plain, (![A_47]: (k4_xboole_0(A_47, k1_zfmisc_1(k3_tarski(A_47)))=k5_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_146, c_366])).
% 6.04/2.42  tff(c_387, plain, (![A_47]: (k5_xboole_0(A_47, A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_375])).
% 6.04/2.42  tff(c_871, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k5_xboole_0(A_116, B_117), C_118)=k5_xboole_0(A_116, k5_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.04/2.42  tff(c_915, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k5_xboole_0(B_117, k5_xboole_0(A_116, B_117)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_387, c_871])).
% 6.04/2.42  tff(c_20, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.04/2.42  tff(c_258, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_242])).
% 6.04/2.42  tff(c_32, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.04/2.42  tff(c_486, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k4_xboole_0(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.04/2.42  tff(c_513, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_486])).
% 6.04/2.42  tff(c_518, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_513])).
% 6.04/2.42  tff(c_770, plain, (![A_24]: (k5_xboole_0(A_24, k3_xboole_0(A_24, k1_xboole_0))=k2_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_731])).
% 6.04/2.42  tff(c_778, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_518, c_770])).
% 6.04/2.42  tff(c_407, plain, (![A_93, B_94]: (k2_xboole_0(A_93, k4_xboole_0(B_94, A_93))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.04/2.42  tff(c_419, plain, (![B_12]: (k2_xboole_0(B_12, k1_xboole_0)=k2_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_258, c_407])).
% 6.04/2.42  tff(c_781, plain, (![B_12]: (k2_xboole_0(B_12, B_12)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_778, c_419])).
% 6.04/2.42  tff(c_147, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_20, c_135])).
% 6.04/2.42  tff(c_761, plain, (![B_12]: (k5_xboole_0(k5_xboole_0(B_12, B_12), B_12)=k2_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_147, c_731])).
% 6.04/2.42  tff(c_777, plain, (![B_12]: (k5_xboole_0(k1_xboole_0, B_12)=k2_xboole_0(B_12, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_761])).
% 6.04/2.42  tff(c_955, plain, (![B_12]: (k5_xboole_0(k1_xboole_0, B_12)=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_781, c_777])).
% 6.04/2.42  tff(c_911, plain, (![A_47, C_118]: (k5_xboole_0(A_47, k5_xboole_0(A_47, C_118))=k5_xboole_0(k1_xboole_0, C_118))), inference(superposition, [status(thm), theory('equality')], [c_387, c_871])).
% 6.04/2.42  tff(c_2556, plain, (![A_190, C_191]: (k5_xboole_0(A_190, k5_xboole_0(A_190, C_191))=C_191)), inference(demodulation, [status(thm), theory('equality')], [c_955, c_911])).
% 6.04/2.42  tff(c_2596, plain, (![B_117, A_116]: (k5_xboole_0(B_117, k5_xboole_0(A_116, B_117))=k5_xboole_0(A_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_915, c_2556])).
% 6.04/2.42  tff(c_2649, plain, (![B_192, A_193]: (k5_xboole_0(B_192, k5_xboole_0(A_193, B_192))=A_193)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2596])).
% 6.04/2.42  tff(c_2555, plain, (![A_47, C_118]: (k5_xboole_0(A_47, k5_xboole_0(A_47, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_955, c_911])).
% 6.04/2.42  tff(c_2658, plain, (![B_192, A_193]: (k5_xboole_0(B_192, A_193)=k5_xboole_0(A_193, B_192))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_2555])).
% 6.04/2.42  tff(c_228, plain, (![A_71, B_72]: (r1_tarski(k1_tarski(A_71), B_72) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.04/2.42  tff(c_28, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.04/2.42  tff(c_236, plain, (![A_71, B_72]: (k3_xboole_0(k1_tarski(A_71), B_72)=k1_tarski(A_71) | ~r2_hidden(A_71, B_72))), inference(resolution, [status(thm)], [c_228, c_28])).
% 6.04/2.42  tff(c_384, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_366])).
% 6.04/2.42  tff(c_3225, plain, (![B_205, A_206]: (k5_xboole_0(B_205, k4_xboole_0(B_205, A_206))=k3_xboole_0(A_206, B_205))), inference(superposition, [status(thm), theory('equality')], [c_384, c_2556])).
% 6.04/2.42  tff(c_2640, plain, (![B_117, A_116]: (k5_xboole_0(B_117, k5_xboole_0(A_116, B_117))=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2596])).
% 6.04/2.42  tff(c_6318, plain, (![B_258, A_259]: (k5_xboole_0(k4_xboole_0(B_258, A_259), k3_xboole_0(A_259, B_258))=B_258)), inference(superposition, [status(thm), theory('equality')], [c_3225, c_2640])).
% 6.04/2.42  tff(c_6392, plain, (![B_72, A_71]: (k5_xboole_0(k4_xboole_0(B_72, k1_tarski(A_71)), k1_tarski(A_71))=B_72 | ~r2_hidden(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_236, c_6318])).
% 6.04/2.42  tff(c_6467, plain, (![A_71, B_72]: (k2_xboole_0(k1_tarski(A_71), B_72)=B_72 | ~r2_hidden(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_5210, c_2658, c_6392])).
% 6.04/2.42  tff(c_40, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.04/2.42  tff(c_1076, plain, (![A_127, B_128]: (r2_hidden('#skF_1'(A_127, B_128), B_128) | r2_hidden('#skF_2'(A_127, B_128), A_127) | B_128=A_127)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.04/2.42  tff(c_38, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.04/2.42  tff(c_324, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, k3_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.04/2.42  tff(c_337, plain, (![B_85, C_86]: (~r1_xboole_0(B_85, B_85) | ~r2_hidden(C_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_147, c_324])).
% 6.04/2.42  tff(c_345, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_337])).
% 6.04/2.42  tff(c_1206, plain, (![B_138]: (r2_hidden('#skF_1'(k1_xboole_0, B_138), B_138) | k1_xboole_0=B_138)), inference(resolution, [status(thm)], [c_1076, c_345])).
% 6.04/2.42  tff(c_14, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.04/2.42  tff(c_1222, plain, (![A_139, B_140]: (~r1_xboole_0(A_139, B_140) | k3_xboole_0(A_139, B_140)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1206, c_14])).
% 6.04/2.42  tff(c_1249, plain, (![A_141, B_142]: (k3_xboole_0(k4_xboole_0(A_141, B_142), B_142)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1222])).
% 6.04/2.42  tff(c_1275, plain, (![B_142, A_141]: (k3_xboole_0(B_142, k4_xboole_0(A_141, B_142))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1249, c_2])).
% 6.04/2.42  tff(c_5241, plain, (![B_243, A_244]: (k5_xboole_0(B_243, k4_xboole_0(A_244, B_243))=k2_xboole_0(B_243, A_244))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5088])).
% 6.04/2.42  tff(c_5545, plain, (![B_248, A_249]: (k5_xboole_0(B_248, k2_xboole_0(B_248, A_249))=k4_xboole_0(A_249, B_248))), inference(superposition, [status(thm), theory('equality')], [c_5241, c_2555])).
% 6.04/2.42  tff(c_5996, plain, (![B_254, A_255]: (k5_xboole_0(k2_xboole_0(B_254, A_255), k4_xboole_0(A_255, B_254))=B_254)), inference(superposition, [status(thm), theory('equality')], [c_5545, c_2640])).
% 6.04/2.42  tff(c_8284, plain, (![A_282, B_283]: (k5_xboole_0(k4_xboole_0(A_282, B_283), B_283)=k2_xboole_0(B_283, A_282))), inference(superposition, [status(thm), theory('equality')], [c_5996, c_2640])).
% 6.04/2.42  tff(c_767, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_731])).
% 6.04/2.42  tff(c_8294, plain, (![B_283, A_282]: (k5_xboole_0(k2_xboole_0(B_283, A_282), k3_xboole_0(B_283, k4_xboole_0(A_282, B_283)))=k2_xboole_0(k4_xboole_0(A_282, B_283), B_283))), inference(superposition, [status(thm), theory('equality')], [c_8284, c_767])).
% 6.04/2.42  tff(c_8400, plain, (![A_282, B_283]: (k2_xboole_0(k4_xboole_0(A_282, B_283), B_283)=k2_xboole_0(B_283, A_282))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1275, c_8294])).
% 6.04/2.42  tff(c_62, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.04/2.42  tff(c_9208, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8400, c_62])).
% 6.04/2.42  tff(c_9331, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6467, c_9208])).
% 6.04/2.42  tff(c_9335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_9331])).
% 6.04/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.42  
% 6.04/2.42  Inference rules
% 6.04/2.42  ----------------------
% 6.04/2.42  #Ref     : 0
% 6.04/2.42  #Sup     : 2285
% 6.04/2.42  #Fact    : 0
% 6.04/2.42  #Define  : 0
% 6.04/2.42  #Split   : 0
% 6.04/2.42  #Chain   : 0
% 6.04/2.42  #Close   : 0
% 6.04/2.42  
% 6.04/2.42  Ordering : KBO
% 6.04/2.42  
% 6.04/2.42  Simplification rules
% 6.04/2.42  ----------------------
% 6.04/2.42  #Subsume      : 98
% 6.04/2.42  #Demod        : 2298
% 6.04/2.42  #Tautology    : 1557
% 6.04/2.42  #SimpNegUnit  : 29
% 6.04/2.42  #BackRed      : 10
% 6.04/2.42  
% 6.04/2.42  #Partial instantiations: 0
% 6.04/2.42  #Strategies tried      : 1
% 6.04/2.42  
% 6.04/2.42  Timing (in seconds)
% 6.04/2.42  ----------------------
% 6.04/2.42  Preprocessing        : 0.33
% 6.04/2.42  Parsing              : 0.18
% 6.04/2.42  CNF conversion       : 0.02
% 6.04/2.42  Main loop            : 1.25
% 6.04/2.42  Inferencing          : 0.36
% 6.04/2.42  Reduction            : 0.59
% 6.04/2.42  Demodulation         : 0.49
% 6.04/2.42  BG Simplification    : 0.04
% 6.04/2.42  Subsumption          : 0.19
% 6.04/2.42  Abstraction          : 0.06
% 6.04/2.42  MUC search           : 0.00
% 6.04/2.42  Cooper               : 0.00
% 6.04/2.42  Total                : 1.63
% 6.04/2.42  Index Insertion      : 0.00
% 6.04/2.42  Index Deletion       : 0.00
% 6.04/2.42  Index Matching       : 0.00
% 6.04/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
