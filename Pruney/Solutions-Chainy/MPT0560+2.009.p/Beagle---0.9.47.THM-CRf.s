%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 39.89s
% Output     : CNFRefutation 40.01s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 532 expanded)
%              Number of leaves         :   35 ( 201 expanded)
%              Depth                    :   22
%              Number of atoms          :  231 ( 972 expanded)
%              Number of equality atoms :   62 ( 311 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_257,plain,(
    ! [A_87] :
      ( k9_relat_1(A_87,k1_relat_1(A_87)) = k2_relat_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_266,plain,(
    ! [A_40] :
      ( k9_relat_1(k6_relat_1(A_40),A_40) = k2_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_257])).

tff(c_270,plain,(
    ! [A_40] : k9_relat_1(k6_relat_1(A_40),A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32,c_266])).

tff(c_54,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_111,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(A_64,B_65) = B_65
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(k2_xboole_0(A_74,B_76),C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,(
    ! [A_74,B_76] : r1_tarski(A_74,k2_xboole_0(A_74,B_76)) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_687,plain,(
    ! [B_118,A_119] :
      ( k7_relat_1(B_118,A_119) = B_118
      | ~ r1_tarski(k1_relat_1(B_118),A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_854,plain,(
    ! [B_128,B_129] :
      ( k7_relat_1(B_128,k2_xboole_0(k1_relat_1(B_128),B_129)) = B_128
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_164,c_687])).

tff(c_904,plain,(
    ! [A_40,B_129] :
      ( k7_relat_1(k6_relat_1(A_40),k2_xboole_0(A_40,B_129)) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_854])).

tff(c_1057,plain,(
    ! [A_137,B_138] : k7_relat_1(k6_relat_1(A_137),k2_xboole_0(A_137,B_138)) = k6_relat_1(A_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_904])).

tff(c_1118,plain,(
    k7_relat_1(k6_relat_1('#skF_5'),'#skF_6') = k6_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1057])).

tff(c_46,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_relat_1(A_48),B_49) = k7_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1783,plain,(
    ! [B_168,C_169,A_170] :
      ( k9_relat_1(k5_relat_1(B_168,C_169),A_170) = k9_relat_1(C_169,k9_relat_1(B_168,A_170))
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1796,plain,(
    ! [B_49,A_48,A_170] :
      ( k9_relat_1(B_49,k9_relat_1(k6_relat_1(A_48),A_170)) = k9_relat_1(k7_relat_1(B_49,A_48),A_170)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1783])).

tff(c_3103,plain,(
    ! [B_236,A_237,A_238] :
      ( k9_relat_1(B_236,k9_relat_1(k6_relat_1(A_237),A_238)) = k9_relat_1(k7_relat_1(B_236,A_237),A_238)
      | ~ v1_relat_1(B_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1796])).

tff(c_3161,plain,(
    ! [B_236,A_40] :
      ( k9_relat_1(k7_relat_1(B_236,A_40),A_40) = k9_relat_1(B_236,A_40)
      | ~ v1_relat_1(B_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_3103])).

tff(c_469,plain,(
    ! [A_101,B_102] :
      ( k5_relat_1(k6_relat_1(A_101),B_102) = k7_relat_1(B_102,A_101)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k5_relat_1(B_42,k6_relat_1(A_41)),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_476,plain,(
    ! [A_41,A_101] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_41),A_101),k6_relat_1(A_101))
      | ~ v1_relat_1(k6_relat_1(A_101))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_36])).

tff(c_485,plain,(
    ! [A_41,A_101] : r1_tarski(k7_relat_1(k6_relat_1(A_41),A_101),k6_relat_1(A_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_476])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_701,plain,(
    ! [A_40,A_119] :
      ( k7_relat_1(k6_relat_1(A_40),A_119) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_119)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_687])).

tff(c_710,plain,(
    ! [A_40,A_119] :
      ( k7_relat_1(k6_relat_1(A_40),A_119) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_701])).

tff(c_962,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden(A_132,B_133)
      | ~ r2_hidden(A_132,k1_relat_1(k7_relat_1(C_134,B_133)))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_968,plain,(
    ! [A_132,A_119,A_40] :
      ( r2_hidden(A_132,A_119)
      | ~ r2_hidden(A_132,k1_relat_1(k6_relat_1(A_40)))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_962])).

tff(c_1494,plain,(
    ! [A_156,A_157,A_158] :
      ( r2_hidden(A_156,A_157)
      | ~ r2_hidden(A_156,A_158)
      | ~ r1_tarski(A_158,A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_968])).

tff(c_1506,plain,(
    ! [A_8,A_157] :
      ( r2_hidden('#skF_1'(A_8),A_157)
      | ~ r1_tarski(A_8,A_157)
      | v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_1494])).

tff(c_1468,plain,(
    ! [A_154,B_155] :
      ( k4_tarski('#skF_2'(A_154,B_155),'#skF_3'(A_154,B_155)) = B_155
      | ~ r2_hidden(B_155,A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [C_21,D_22,A_8] :
      ( k4_tarski(C_21,D_22) != '#skF_1'(A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1472,plain,(
    ! [B_155,A_8,A_154] :
      ( B_155 != '#skF_1'(A_8)
      | v1_relat_1(A_8)
      | ~ r2_hidden(B_155,A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_14])).

tff(c_2576,plain,(
    ! [A_210,A_211] :
      ( v1_relat_1(A_210)
      | ~ r2_hidden('#skF_1'(A_210),A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1472])).

tff(c_2664,plain,(
    ! [A_216,A_217] :
      ( ~ v1_relat_1(A_216)
      | ~ r1_tarski(A_217,A_216)
      | v1_relat_1(A_217) ) ),
    inference(resolution,[status(thm)],[c_1506,c_2576])).

tff(c_2742,plain,(
    ! [A_101,A_41] :
      ( ~ v1_relat_1(k6_relat_1(A_101))
      | v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_101)) ) ),
    inference(resolution,[status(thm)],[c_485,c_2664])).

tff(c_2834,plain,(
    ! [A_41,A_101] : v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2742])).

tff(c_2140,plain,(
    ! [B_187,A_188,C_189] :
      ( r1_tarski(k9_relat_1(B_187,A_188),k9_relat_1(C_189,A_188))
      | ~ r1_tarski(B_187,C_189)
      | ~ v1_relat_1(C_189)
      | ~ v1_relat_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5434,plain,(
    ! [B_320,A_321,C_322] :
      ( k2_xboole_0(k9_relat_1(B_320,A_321),k9_relat_1(C_322,A_321)) = k9_relat_1(C_322,A_321)
      | ~ r1_tarski(B_320,C_322)
      | ~ v1_relat_1(C_322)
      | ~ v1_relat_1(B_320) ) ),
    inference(resolution,[status(thm)],[c_2140,c_10])).

tff(c_5564,plain,(
    ! [A_40,B_320] :
      ( k9_relat_1(k6_relat_1(A_40),A_40) = k2_xboole_0(k9_relat_1(B_320,A_40),A_40)
      | ~ r1_tarski(B_320,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(B_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_5434])).

tff(c_15043,plain,(
    ! [B_615,A_616] :
      ( k2_xboole_0(k9_relat_1(B_615,A_616),A_616) = A_616
      | ~ r1_tarski(B_615,k6_relat_1(A_616))
      | ~ v1_relat_1(B_615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_270,c_5564])).

tff(c_15170,plain,(
    ! [A_41,A_101] :
      ( k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_41),A_101),A_101),A_101) = A_101
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_41),A_101)) ) ),
    inference(resolution,[status(thm)],[c_485,c_15043])).

tff(c_15740,plain,(
    ! [A_622,A_623] : k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_622),A_623),A_623),A_623) = A_623 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2834,c_15170])).

tff(c_15894,plain,(
    ! [A_622,A_40] :
      ( k2_xboole_0(k9_relat_1(k6_relat_1(A_622),A_40),A_40) = A_40
      | ~ v1_relat_1(k6_relat_1(A_622)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3161,c_15740])).

tff(c_15946,plain,(
    ! [A_624,A_625] : k2_xboole_0(k9_relat_1(k6_relat_1(A_624),A_625),A_625) = A_625 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_15894])).

tff(c_874,plain,(
    ! [A_41,B_129] :
      ( r1_tarski(k6_relat_1(A_41),k6_relat_1(k2_xboole_0(k1_relat_1(k6_relat_1(A_41)),B_129)))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_485])).

tff(c_913,plain,(
    ! [A_41,B_129] : r1_tarski(k6_relat_1(A_41),k6_relat_1(k2_xboole_0(A_41,B_129))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_874])).

tff(c_16067,plain,(
    ! [A_624,A_625] : r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1(A_624),A_625)),k6_relat_1(A_625)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15946,c_913])).

tff(c_34,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_41),B_42),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_920,plain,(
    ! [A_40,B_129] : k7_relat_1(k6_relat_1(A_40),k2_xboole_0(A_40,B_129)) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_904])).

tff(c_487,plain,(
    ! [A_103,A_104] : r1_tarski(k7_relat_1(k6_relat_1(A_103),A_104),k6_relat_1(A_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_476])).

tff(c_501,plain,(
    ! [A_103,A_104] : k2_xboole_0(k7_relat_1(k6_relat_1(A_103),A_104),k6_relat_1(A_104)) = k6_relat_1(A_104) ),
    inference(resolution,[status(thm)],[c_487,c_10])).

tff(c_280,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_89,A_90)),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_656,plain,(
    ! [B_116,A_117] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_116,A_117)),A_117) = A_117
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_280,c_10])).

tff(c_165,plain,(
    ! [A_77,B_78] : r1_tarski(A_77,k2_xboole_0(A_77,B_78)) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_181,plain,(
    ! [A_3,B_4,B_78] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_78)) ),
    inference(resolution,[status(thm)],[c_165,c_8])).

tff(c_4093,plain,(
    ! [B_270,A_271,B_272] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_270,A_271)),k2_xboole_0(A_271,B_272))
      | ~ v1_relat_1(B_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_181])).

tff(c_4143,plain,(
    ! [A_40,A_119,B_272] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_40)),k2_xboole_0(A_119,B_272))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_4093])).

tff(c_4281,plain,(
    ! [A_276,A_277,B_278] :
      ( r1_tarski(A_276,k2_xboole_0(A_277,B_278))
      | ~ r1_tarski(A_276,A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_4143])).

tff(c_2606,plain,(
    ! [A_157,A_8] :
      ( ~ v1_relat_1(A_157)
      | ~ r1_tarski(A_8,A_157)
      | v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_1506,c_2576])).

tff(c_5702,plain,(
    ! [A_329,B_330,A_331] :
      ( ~ v1_relat_1(k2_xboole_0(A_329,B_330))
      | v1_relat_1(A_331)
      | ~ r1_tarski(A_331,A_329) ) ),
    inference(resolution,[status(thm)],[c_4281,c_2606])).

tff(c_5716,plain,(
    ! [A_104,A_331,A_103] :
      ( ~ v1_relat_1(k6_relat_1(A_104))
      | v1_relat_1(A_331)
      | ~ r1_tarski(A_331,k7_relat_1(k6_relat_1(A_103),A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_5702])).

tff(c_5820,plain,(
    ! [A_333,A_334,A_335] :
      ( v1_relat_1(A_333)
      | ~ r1_tarski(A_333,k7_relat_1(k6_relat_1(A_334),A_335)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5716])).

tff(c_5895,plain,(
    ! [A_336,A_337] :
      ( v1_relat_1(A_336)
      | ~ r1_tarski(A_336,k6_relat_1(A_337)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_5820])).

tff(c_5986,plain,(
    ! [A_41,A_337] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_337)))
      | ~ v1_relat_1(k6_relat_1(A_337)) ) ),
    inference(resolution,[status(thm)],[c_34,c_5895])).

tff(c_6048,plain,(
    ! [A_41,A_337] : v1_relat_1(k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_337))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5986])).

tff(c_145,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_72),B_73),B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2880,plain,(
    ! [A_220,B_221] :
      ( k5_relat_1(k6_relat_1(A_220),B_221) = B_221
      | ~ r1_tarski(B_221,k5_relat_1(k6_relat_1(A_220),B_221))
      | ~ v1_relat_1(B_221) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_20088,plain,(
    ! [A_708,B_709] :
      ( k5_relat_1(k6_relat_1(A_708),B_709) = B_709
      | ~ r1_tarski(B_709,k7_relat_1(B_709,A_708))
      | ~ v1_relat_1(B_709)
      | ~ v1_relat_1(B_709) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2880])).

tff(c_20137,plain,
    ( k5_relat_1(k6_relat_1('#skF_6'),k6_relat_1('#skF_5')) = k6_relat_1('#skF_5')
    | ~ r1_tarski(k6_relat_1('#skF_5'),k6_relat_1('#skF_5'))
    | ~ v1_relat_1(k6_relat_1('#skF_5'))
    | ~ v1_relat_1(k6_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_20088])).

tff(c_20183,plain,(
    k5_relat_1(k6_relat_1('#skF_6'),k6_relat_1('#skF_5')) = k6_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_6,c_20137])).

tff(c_22,plain,(
    ! [A_29] :
      ( k9_relat_1(A_29,k1_relat_1(A_29)) = k2_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1800,plain,(
    ! [C_169,B_168] :
      ( k9_relat_1(C_169,k9_relat_1(B_168,k1_relat_1(k5_relat_1(B_168,C_169)))) = k2_relat_1(k5_relat_1(B_168,C_169))
      | ~ v1_relat_1(C_169)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(k5_relat_1(B_168,C_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1783])).

tff(c_20386,plain,
    ( k9_relat_1(k6_relat_1('#skF_5'),k9_relat_1(k6_relat_1('#skF_6'),k1_relat_1(k6_relat_1('#skF_5')))) = k2_relat_1(k5_relat_1(k6_relat_1('#skF_6'),k6_relat_1('#skF_5')))
    | ~ v1_relat_1(k6_relat_1('#skF_5'))
    | ~ v1_relat_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'),k6_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20183,c_1800])).

tff(c_20450,plain,(
    k9_relat_1(k6_relat_1('#skF_5'),k9_relat_1(k6_relat_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6048,c_18,c_18,c_32,c_20183,c_30,c_20386])).

tff(c_20746,plain,(
    r1_tarski(k6_relat_1('#skF_5'),k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20450,c_16067])).

tff(c_20952,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'),'#skF_5')) = k6_relat_1('#skF_5')
    | ~ r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'),'#skF_5')),k6_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20746,c_2])).

tff(c_20978,plain,(
    k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'),'#skF_5')) = k6_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16067,c_20952])).

tff(c_3128,plain,(
    ! [A_237,A_238] :
      ( k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237),A_238)),A_237),A_238) = k9_relat_1(k6_relat_1(A_237),A_238)
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237),A_238))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3103,c_270])).

tff(c_3176,plain,(
    ! [A_237,A_238] : k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237),A_238)),A_237),A_238) = k9_relat_1(k6_relat_1(A_237),A_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3128])).

tff(c_21053,plain,(
    k9_relat_1(k7_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_5') = k9_relat_1(k6_relat_1('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20978,c_3176])).

tff(c_21427,plain,(
    k9_relat_1(k6_relat_1('#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_1118,c_21053])).

tff(c_1804,plain,(
    ! [B_49,A_48,A_170] :
      ( k9_relat_1(B_49,k9_relat_1(k6_relat_1(A_48),A_170)) = k9_relat_1(k7_relat_1(B_49,A_48),A_170)
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1796])).

tff(c_113071,plain,(
    ! [B_1841] :
      ( k9_relat_1(k7_relat_1(B_1841,'#skF_6'),'#skF_5') = k9_relat_1(B_1841,'#skF_5')
      | ~ v1_relat_1(B_1841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21427,c_1804])).

tff(c_52,plain,(
    k9_relat_1(k7_relat_1('#skF_4','#skF_6'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_113316,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_113071,c_52])).

tff(c_113390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_113316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.89/30.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.01/30.83  
% 40.01/30.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.01/30.83  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 40.01/30.83  
% 40.01/30.83  %Foreground sorts:
% 40.01/30.83  
% 40.01/30.83  
% 40.01/30.83  %Background operators:
% 40.01/30.83  
% 40.01/30.83  
% 40.01/30.83  %Foreground operators:
% 40.01/30.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.01/30.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.01/30.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 40.01/30.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 40.01/30.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 40.01/30.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 40.01/30.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 40.01/30.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.01/30.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 40.01/30.83  tff('#skF_5', type, '#skF_5': $i).
% 40.01/30.83  tff('#skF_6', type, '#skF_6': $i).
% 40.01/30.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 40.01/30.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.01/30.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.01/30.83  tff('#skF_4', type, '#skF_4': $i).
% 40.01/30.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 40.01/30.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.01/30.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 40.01/30.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 40.01/30.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.01/30.83  
% 40.01/30.86  tff(f_123, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 40.01/30.86  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 40.01/30.86  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 40.01/30.86  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 40.01/30.86  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 40.01/30.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 40.01/30.86  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 40.01/30.86  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 40.01/30.86  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 40.01/30.86  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 40.01/30.86  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 40.01/30.86  tff(f_49, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 40.01/30.86  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 40.01/30.86  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 40.01/30.86  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 40.01/30.86  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 40.01/30.86  tff(c_18, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 40.01/30.86  tff(c_32, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.01/30.86  tff(c_30, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.01/30.86  tff(c_257, plain, (![A_87]: (k9_relat_1(A_87, k1_relat_1(A_87))=k2_relat_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.01/30.86  tff(c_266, plain, (![A_40]: (k9_relat_1(k6_relat_1(A_40), A_40)=k2_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_257])).
% 40.01/30.86  tff(c_270, plain, (![A_40]: (k9_relat_1(k6_relat_1(A_40), A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32, c_266])).
% 40.01/30.86  tff(c_54, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 40.01/30.86  tff(c_111, plain, (![A_64, B_65]: (k2_xboole_0(A_64, B_65)=B_65 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.01/30.86  tff(c_119, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_54, c_111])).
% 40.01/30.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.01/30.86  tff(c_153, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(k2_xboole_0(A_74, B_76), C_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.01/30.86  tff(c_164, plain, (![A_74, B_76]: (r1_tarski(A_74, k2_xboole_0(A_74, B_76)))), inference(resolution, [status(thm)], [c_6, c_153])).
% 40.01/30.86  tff(c_687, plain, (![B_118, A_119]: (k7_relat_1(B_118, A_119)=B_118 | ~r1_tarski(k1_relat_1(B_118), A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 40.01/30.86  tff(c_854, plain, (![B_128, B_129]: (k7_relat_1(B_128, k2_xboole_0(k1_relat_1(B_128), B_129))=B_128 | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_164, c_687])).
% 40.01/30.86  tff(c_904, plain, (![A_40, B_129]: (k7_relat_1(k6_relat_1(A_40), k2_xboole_0(A_40, B_129))=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_854])).
% 40.01/30.86  tff(c_1057, plain, (![A_137, B_138]: (k7_relat_1(k6_relat_1(A_137), k2_xboole_0(A_137, B_138))=k6_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_904])).
% 40.01/30.86  tff(c_1118, plain, (k7_relat_1(k6_relat_1('#skF_5'), '#skF_6')=k6_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_119, c_1057])).
% 40.01/30.86  tff(c_46, plain, (![A_48, B_49]: (k5_relat_1(k6_relat_1(A_48), B_49)=k7_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_105])).
% 40.01/30.86  tff(c_1783, plain, (![B_168, C_169, A_170]: (k9_relat_1(k5_relat_1(B_168, C_169), A_170)=k9_relat_1(C_169, k9_relat_1(B_168, A_170)) | ~v1_relat_1(C_169) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.01/30.86  tff(c_1796, plain, (![B_49, A_48, A_170]: (k9_relat_1(B_49, k9_relat_1(k6_relat_1(A_48), A_170))=k9_relat_1(k7_relat_1(B_49, A_48), A_170) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1783])).
% 40.01/30.86  tff(c_3103, plain, (![B_236, A_237, A_238]: (k9_relat_1(B_236, k9_relat_1(k6_relat_1(A_237), A_238))=k9_relat_1(k7_relat_1(B_236, A_237), A_238) | ~v1_relat_1(B_236))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1796])).
% 40.01/30.86  tff(c_3161, plain, (![B_236, A_40]: (k9_relat_1(k7_relat_1(B_236, A_40), A_40)=k9_relat_1(B_236, A_40) | ~v1_relat_1(B_236))), inference(superposition, [status(thm), theory('equality')], [c_270, c_3103])).
% 40.01/30.86  tff(c_469, plain, (![A_101, B_102]: (k5_relat_1(k6_relat_1(A_101), B_102)=k7_relat_1(B_102, A_101) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_105])).
% 40.01/30.86  tff(c_36, plain, (![B_42, A_41]: (r1_tarski(k5_relat_1(B_42, k6_relat_1(A_41)), B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.01/30.86  tff(c_476, plain, (![A_41, A_101]: (r1_tarski(k7_relat_1(k6_relat_1(A_41), A_101), k6_relat_1(A_101)) | ~v1_relat_1(k6_relat_1(A_101)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_469, c_36])).
% 40.01/30.86  tff(c_485, plain, (![A_41, A_101]: (r1_tarski(k7_relat_1(k6_relat_1(A_41), A_101), k6_relat_1(A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_476])).
% 40.01/30.86  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.01/30.86  tff(c_701, plain, (![A_40, A_119]: (k7_relat_1(k6_relat_1(A_40), A_119)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_119) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_687])).
% 40.01/30.86  tff(c_710, plain, (![A_40, A_119]: (k7_relat_1(k6_relat_1(A_40), A_119)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_701])).
% 40.01/30.86  tff(c_962, plain, (![A_132, B_133, C_134]: (r2_hidden(A_132, B_133) | ~r2_hidden(A_132, k1_relat_1(k7_relat_1(C_134, B_133))) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_97])).
% 40.01/30.86  tff(c_968, plain, (![A_132, A_119, A_40]: (r2_hidden(A_132, A_119) | ~r2_hidden(A_132, k1_relat_1(k6_relat_1(A_40))) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, A_119))), inference(superposition, [status(thm), theory('equality')], [c_710, c_962])).
% 40.01/30.86  tff(c_1494, plain, (![A_156, A_157, A_158]: (r2_hidden(A_156, A_157) | ~r2_hidden(A_156, A_158) | ~r1_tarski(A_158, A_157))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30, c_968])).
% 40.01/30.86  tff(c_1506, plain, (![A_8, A_157]: (r2_hidden('#skF_1'(A_8), A_157) | ~r1_tarski(A_8, A_157) | v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_1494])).
% 40.01/30.86  tff(c_1468, plain, (![A_154, B_155]: (k4_tarski('#skF_2'(A_154, B_155), '#skF_3'(A_154, B_155))=B_155 | ~r2_hidden(B_155, A_154) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.01/30.86  tff(c_14, plain, (![C_21, D_22, A_8]: (k4_tarski(C_21, D_22)!='#skF_1'(A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 40.01/30.86  tff(c_1472, plain, (![B_155, A_8, A_154]: (B_155!='#skF_1'(A_8) | v1_relat_1(A_8) | ~r2_hidden(B_155, A_154) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_1468, c_14])).
% 40.01/30.86  tff(c_2576, plain, (![A_210, A_211]: (v1_relat_1(A_210) | ~r2_hidden('#skF_1'(A_210), A_211) | ~v1_relat_1(A_211))), inference(reflexivity, [status(thm), theory('equality')], [c_1472])).
% 40.01/30.86  tff(c_2664, plain, (![A_216, A_217]: (~v1_relat_1(A_216) | ~r1_tarski(A_217, A_216) | v1_relat_1(A_217))), inference(resolution, [status(thm)], [c_1506, c_2576])).
% 40.01/30.86  tff(c_2742, plain, (![A_101, A_41]: (~v1_relat_1(k6_relat_1(A_101)) | v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_101)))), inference(resolution, [status(thm)], [c_485, c_2664])).
% 40.01/30.86  tff(c_2834, plain, (![A_41, A_101]: (v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2742])).
% 40.01/30.86  tff(c_2140, plain, (![B_187, A_188, C_189]: (r1_tarski(k9_relat_1(B_187, A_188), k9_relat_1(C_189, A_188)) | ~r1_tarski(B_187, C_189) | ~v1_relat_1(C_189) | ~v1_relat_1(B_187))), inference(cnfTransformation, [status(thm)], [f_72])).
% 40.01/30.86  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.01/30.86  tff(c_5434, plain, (![B_320, A_321, C_322]: (k2_xboole_0(k9_relat_1(B_320, A_321), k9_relat_1(C_322, A_321))=k9_relat_1(C_322, A_321) | ~r1_tarski(B_320, C_322) | ~v1_relat_1(C_322) | ~v1_relat_1(B_320))), inference(resolution, [status(thm)], [c_2140, c_10])).
% 40.01/30.86  tff(c_5564, plain, (![A_40, B_320]: (k9_relat_1(k6_relat_1(A_40), A_40)=k2_xboole_0(k9_relat_1(B_320, A_40), A_40) | ~r1_tarski(B_320, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(B_320))), inference(superposition, [status(thm), theory('equality')], [c_270, c_5434])).
% 40.01/30.86  tff(c_15043, plain, (![B_615, A_616]: (k2_xboole_0(k9_relat_1(B_615, A_616), A_616)=A_616 | ~r1_tarski(B_615, k6_relat_1(A_616)) | ~v1_relat_1(B_615))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_270, c_5564])).
% 40.01/30.86  tff(c_15170, plain, (![A_41, A_101]: (k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_41), A_101), A_101), A_101)=A_101 | ~v1_relat_1(k7_relat_1(k6_relat_1(A_41), A_101)))), inference(resolution, [status(thm)], [c_485, c_15043])).
% 40.01/30.86  tff(c_15740, plain, (![A_622, A_623]: (k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_622), A_623), A_623), A_623)=A_623)), inference(demodulation, [status(thm), theory('equality')], [c_2834, c_15170])).
% 40.01/30.86  tff(c_15894, plain, (![A_622, A_40]: (k2_xboole_0(k9_relat_1(k6_relat_1(A_622), A_40), A_40)=A_40 | ~v1_relat_1(k6_relat_1(A_622)))), inference(superposition, [status(thm), theory('equality')], [c_3161, c_15740])).
% 40.01/30.86  tff(c_15946, plain, (![A_624, A_625]: (k2_xboole_0(k9_relat_1(k6_relat_1(A_624), A_625), A_625)=A_625)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_15894])).
% 40.01/30.86  tff(c_874, plain, (![A_41, B_129]: (r1_tarski(k6_relat_1(A_41), k6_relat_1(k2_xboole_0(k1_relat_1(k6_relat_1(A_41)), B_129))) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_854, c_485])).
% 40.01/30.86  tff(c_913, plain, (![A_41, B_129]: (r1_tarski(k6_relat_1(A_41), k6_relat_1(k2_xboole_0(A_41, B_129))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30, c_874])).
% 40.01/30.86  tff(c_16067, plain, (![A_624, A_625]: (r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1(A_624), A_625)), k6_relat_1(A_625)))), inference(superposition, [status(thm), theory('equality')], [c_15946, c_913])).
% 40.01/30.86  tff(c_34, plain, (![A_41, B_42]: (r1_tarski(k5_relat_1(k6_relat_1(A_41), B_42), B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.01/30.86  tff(c_920, plain, (![A_40, B_129]: (k7_relat_1(k6_relat_1(A_40), k2_xboole_0(A_40, B_129))=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_904])).
% 40.01/30.86  tff(c_487, plain, (![A_103, A_104]: (r1_tarski(k7_relat_1(k6_relat_1(A_103), A_104), k6_relat_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_476])).
% 40.01/30.86  tff(c_501, plain, (![A_103, A_104]: (k2_xboole_0(k7_relat_1(k6_relat_1(A_103), A_104), k6_relat_1(A_104))=k6_relat_1(A_104))), inference(resolution, [status(thm)], [c_487, c_10])).
% 40.01/30.86  tff(c_280, plain, (![B_89, A_90]: (r1_tarski(k1_relat_1(k7_relat_1(B_89, A_90)), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_101])).
% 40.01/30.86  tff(c_656, plain, (![B_116, A_117]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_116, A_117)), A_117)=A_117 | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_280, c_10])).
% 40.01/30.86  tff(c_165, plain, (![A_77, B_78]: (r1_tarski(A_77, k2_xboole_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_6, c_153])).
% 40.01/30.86  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.01/30.86  tff(c_181, plain, (![A_3, B_4, B_78]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_78)))), inference(resolution, [status(thm)], [c_165, c_8])).
% 40.01/30.86  tff(c_4093, plain, (![B_270, A_271, B_272]: (r1_tarski(k1_relat_1(k7_relat_1(B_270, A_271)), k2_xboole_0(A_271, B_272)) | ~v1_relat_1(B_270))), inference(superposition, [status(thm), theory('equality')], [c_656, c_181])).
% 40.01/30.86  tff(c_4143, plain, (![A_40, A_119, B_272]: (r1_tarski(k1_relat_1(k6_relat_1(A_40)), k2_xboole_0(A_119, B_272)) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, A_119))), inference(superposition, [status(thm), theory('equality')], [c_710, c_4093])).
% 40.01/30.86  tff(c_4281, plain, (![A_276, A_277, B_278]: (r1_tarski(A_276, k2_xboole_0(A_277, B_278)) | ~r1_tarski(A_276, A_277))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30, c_4143])).
% 40.01/30.86  tff(c_2606, plain, (![A_157, A_8]: (~v1_relat_1(A_157) | ~r1_tarski(A_8, A_157) | v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_1506, c_2576])).
% 40.01/30.86  tff(c_5702, plain, (![A_329, B_330, A_331]: (~v1_relat_1(k2_xboole_0(A_329, B_330)) | v1_relat_1(A_331) | ~r1_tarski(A_331, A_329))), inference(resolution, [status(thm)], [c_4281, c_2606])).
% 40.01/30.86  tff(c_5716, plain, (![A_104, A_331, A_103]: (~v1_relat_1(k6_relat_1(A_104)) | v1_relat_1(A_331) | ~r1_tarski(A_331, k7_relat_1(k6_relat_1(A_103), A_104)))), inference(superposition, [status(thm), theory('equality')], [c_501, c_5702])).
% 40.01/30.86  tff(c_5820, plain, (![A_333, A_334, A_335]: (v1_relat_1(A_333) | ~r1_tarski(A_333, k7_relat_1(k6_relat_1(A_334), A_335)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5716])).
% 40.01/30.86  tff(c_5895, plain, (![A_336, A_337]: (v1_relat_1(A_336) | ~r1_tarski(A_336, k6_relat_1(A_337)))), inference(superposition, [status(thm), theory('equality')], [c_920, c_5820])).
% 40.01/30.86  tff(c_5986, plain, (![A_41, A_337]: (v1_relat_1(k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_337))) | ~v1_relat_1(k6_relat_1(A_337)))), inference(resolution, [status(thm)], [c_34, c_5895])).
% 40.01/30.86  tff(c_6048, plain, (![A_41, A_337]: (v1_relat_1(k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_337))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5986])).
% 40.01/30.86  tff(c_145, plain, (![A_72, B_73]: (r1_tarski(k5_relat_1(k6_relat_1(A_72), B_73), B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.01/30.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.01/30.86  tff(c_2880, plain, (![A_220, B_221]: (k5_relat_1(k6_relat_1(A_220), B_221)=B_221 | ~r1_tarski(B_221, k5_relat_1(k6_relat_1(A_220), B_221)) | ~v1_relat_1(B_221))), inference(resolution, [status(thm)], [c_145, c_2])).
% 40.01/30.86  tff(c_20088, plain, (![A_708, B_709]: (k5_relat_1(k6_relat_1(A_708), B_709)=B_709 | ~r1_tarski(B_709, k7_relat_1(B_709, A_708)) | ~v1_relat_1(B_709) | ~v1_relat_1(B_709))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2880])).
% 40.01/30.86  tff(c_20137, plain, (k5_relat_1(k6_relat_1('#skF_6'), k6_relat_1('#skF_5'))=k6_relat_1('#skF_5') | ~r1_tarski(k6_relat_1('#skF_5'), k6_relat_1('#skF_5')) | ~v1_relat_1(k6_relat_1('#skF_5')) | ~v1_relat_1(k6_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1118, c_20088])).
% 40.01/30.86  tff(c_20183, plain, (k5_relat_1(k6_relat_1('#skF_6'), k6_relat_1('#skF_5'))=k6_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_6, c_20137])).
% 40.01/30.86  tff(c_22, plain, (![A_29]: (k9_relat_1(A_29, k1_relat_1(A_29))=k2_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.01/30.86  tff(c_1800, plain, (![C_169, B_168]: (k9_relat_1(C_169, k9_relat_1(B_168, k1_relat_1(k5_relat_1(B_168, C_169))))=k2_relat_1(k5_relat_1(B_168, C_169)) | ~v1_relat_1(C_169) | ~v1_relat_1(B_168) | ~v1_relat_1(k5_relat_1(B_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1783])).
% 40.01/30.86  tff(c_20386, plain, (k9_relat_1(k6_relat_1('#skF_5'), k9_relat_1(k6_relat_1('#skF_6'), k1_relat_1(k6_relat_1('#skF_5'))))=k2_relat_1(k5_relat_1(k6_relat_1('#skF_6'), k6_relat_1('#skF_5'))) | ~v1_relat_1(k6_relat_1('#skF_5')) | ~v1_relat_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_6'), k6_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_20183, c_1800])).
% 40.01/30.86  tff(c_20450, plain, (k9_relat_1(k6_relat_1('#skF_5'), k9_relat_1(k6_relat_1('#skF_6'), '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6048, c_18, c_18, c_32, c_20183, c_30, c_20386])).
% 40.01/30.86  tff(c_20746, plain, (r1_tarski(k6_relat_1('#skF_5'), k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_20450, c_16067])).
% 40.01/30.86  tff(c_20952, plain, (k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'), '#skF_5'))=k6_relat_1('#skF_5') | ~r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'), '#skF_5')), k6_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_20746, c_2])).
% 40.01/30.86  tff(c_20978, plain, (k6_relat_1(k9_relat_1(k6_relat_1('#skF_6'), '#skF_5'))=k6_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16067, c_20952])).
% 40.01/30.86  tff(c_3128, plain, (![A_237, A_238]: (k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237), A_238)), A_237), A_238)=k9_relat_1(k6_relat_1(A_237), A_238) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237), A_238))))), inference(superposition, [status(thm), theory('equality')], [c_3103, c_270])).
% 40.01/30.86  tff(c_3176, plain, (![A_237, A_238]: (k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_237), A_238)), A_237), A_238)=k9_relat_1(k6_relat_1(A_237), A_238))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3128])).
% 40.01/30.86  tff(c_21053, plain, (k9_relat_1(k7_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_5')=k9_relat_1(k6_relat_1('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20978, c_3176])).
% 40.01/30.86  tff(c_21427, plain, (k9_relat_1(k6_relat_1('#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_1118, c_21053])).
% 40.01/30.86  tff(c_1804, plain, (![B_49, A_48, A_170]: (k9_relat_1(B_49, k9_relat_1(k6_relat_1(A_48), A_170))=k9_relat_1(k7_relat_1(B_49, A_48), A_170) | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1796])).
% 40.01/30.86  tff(c_113071, plain, (![B_1841]: (k9_relat_1(k7_relat_1(B_1841, '#skF_6'), '#skF_5')=k9_relat_1(B_1841, '#skF_5') | ~v1_relat_1(B_1841))), inference(superposition, [status(thm), theory('equality')], [c_21427, c_1804])).
% 40.01/30.86  tff(c_52, plain, (k9_relat_1(k7_relat_1('#skF_4', '#skF_6'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 40.01/30.86  tff(c_113316, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_113071, c_52])).
% 40.01/30.86  tff(c_113390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_113316])).
% 40.01/30.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.01/30.86  
% 40.01/30.86  Inference rules
% 40.01/30.86  ----------------------
% 40.01/30.86  #Ref     : 1
% 40.01/30.86  #Sup     : 27275
% 40.01/30.86  #Fact    : 0
% 40.01/30.86  #Define  : 0
% 40.01/30.86  #Split   : 8
% 40.01/30.86  #Chain   : 0
% 40.01/30.86  #Close   : 0
% 40.01/30.86  
% 40.01/30.86  Ordering : KBO
% 40.01/30.86  
% 40.01/30.86  Simplification rules
% 40.01/30.86  ----------------------
% 40.01/30.86  #Subsume      : 7122
% 40.01/30.86  #Demod        : 18387
% 40.01/30.86  #Tautology    : 6366
% 40.01/30.86  #SimpNegUnit  : 297
% 40.01/30.86  #BackRed      : 22
% 40.01/30.86  
% 40.01/30.86  #Partial instantiations: 0
% 40.01/30.86  #Strategies tried      : 1
% 40.01/30.86  
% 40.01/30.86  Timing (in seconds)
% 40.01/30.86  ----------------------
% 40.01/30.87  Preprocessing        : 0.31
% 40.01/30.87  Parsing              : 0.17
% 40.01/30.87  CNF conversion       : 0.02
% 40.01/30.87  Main loop            : 29.77
% 40.01/30.87  Inferencing          : 2.76
% 40.01/30.87  Reduction            : 15.20
% 40.01/30.87  Demodulation         : 13.37
% 40.01/30.87  BG Simplification    : 0.32
% 40.01/30.87  Subsumption          : 10.47
% 40.01/30.87  Abstraction          : 0.48
% 40.01/30.87  MUC search           : 0.00
% 40.01/30.87  Cooper               : 0.00
% 40.01/30.87  Total                : 30.14
% 40.01/30.87  Index Insertion      : 0.00
% 40.01/30.87  Index Deletion       : 0.00
% 40.01/30.87  Index Matching       : 0.00
% 40.01/30.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
