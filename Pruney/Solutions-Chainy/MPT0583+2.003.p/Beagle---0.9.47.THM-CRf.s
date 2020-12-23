%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 12.74s
% Output     : CNFRefutation 12.97s
% Verified   : 
% Statistics : Number of formulae       :  157 (4013 expanded)
%              Number of leaves         :   44 (1389 expanded)
%              Depth                    :   32
%              Number of atoms          :  224 (6657 expanded)
%              Number of equality atoms :  120 (2958 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(c_64,plain,(
    k7_relat_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_68,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_185,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_82] : r1_tarski(A_82,A_82) ),
    inference(resolution,[status(thm)],[c_185,c_4])).

tff(c_191,plain,(
    ! [A_84] : r1_tarski(A_84,A_84) ),
    inference(resolution,[status(thm)],[c_185,c_4])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_195,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_20])).

tff(c_211,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = B_87
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_226,plain,(
    ! [A_84] :
      ( k2_xboole_0(A_84,k1_xboole_0) = A_84
      | ~ r1_tarski(A_84,A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_211])).

tff(c_236,plain,(
    ! [A_84] : k2_xboole_0(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_226])).

tff(c_30,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),k3_xboole_0(A_6,B_7)) = k5_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),k3_xboole_0(A_20,B_21)) = k2_xboole_0(k4_xboole_0(A_20,B_21),k4_xboole_0(B_21,A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_661,plain,(
    ! [A_132,B_133] : k2_xboole_0(k4_xboole_0(A_132,B_133),k4_xboole_0(B_133,A_132)) = k5_xboole_0(A_132,B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_731,plain,(
    ! [A_19] : k2_xboole_0(k4_xboole_0(A_19,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_661])).

tff(c_742,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_30,c_731])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_237,plain,(
    ! [A_88] : k2_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_226])).

tff(c_16,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_246,plain,(
    ! [A_88] : k3_xboole_0(A_88,A_88) = A_88 ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_16])).

tff(c_426,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_xboole_0(A_110,k3_xboole_0(B_111,C_112))
      | ~ r1_tarski(A_110,k5_xboole_0(B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_432,plain,(
    ! [A_110,A_88] :
      ( r1_xboole_0(A_110,A_88)
      | ~ r1_tarski(A_110,k5_xboole_0(A_88,A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_426])).

tff(c_436,plain,(
    ! [A_110,A_88] :
      ( r1_xboole_0(A_110,A_88)
      | ~ r1_tarski(A_110,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_432])).

tff(c_765,plain,(
    ! [A_136] : k4_xboole_0(A_136,k1_xboole_0) = A_136 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_30,c_731])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1017,plain,(
    ! [A_145] :
      ( k2_xboole_0(k1_xboole_0,A_145) = A_145
      | ~ r1_tarski(k1_xboole_0,A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_24])).

tff(c_1032,plain,(
    ! [B_14] :
      ( k2_xboole_0(k1_xboole_0,B_14) = B_14
      | k4_xboole_0(k1_xboole_0,B_14) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1017])).

tff(c_1041,plain,(
    ! [B_14] : k2_xboole_0(k1_xboole_0,B_14) = B_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1032])).

tff(c_1181,plain,(
    ! [C_153,B_154,A_155] :
      ( k4_xboole_0(k2_xboole_0(C_153,B_154),A_155) = k2_xboole_0(k4_xboole_0(C_153,A_155),B_154)
      | ~ r1_xboole_0(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1226,plain,(
    ! [A_155,B_14] :
      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,A_155),B_14) = k4_xboole_0(B_14,A_155)
      | ~ r1_xboole_0(A_155,B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_1181])).

tff(c_1355,plain,(
    ! [B_167,A_168] :
      ( k4_xboole_0(B_167,A_168) = B_167
      | ~ r1_xboole_0(A_168,B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_26,c_1226])).

tff(c_1393,plain,(
    ! [A_169,A_170] :
      ( k4_xboole_0(A_169,A_170) = A_169
      | ~ r1_tarski(A_170,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_436,c_1355])).

tff(c_1399,plain,(
    ! [A_169,A_13] :
      ( k4_xboole_0(A_169,A_13) = A_169
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1393])).

tff(c_1404,plain,(
    ! [A_169] : k4_xboole_0(A_169,k1_xboole_0) = A_169 ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_1399])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1061,plain,(
    ! [B_150] : k2_xboole_0(k1_xboole_0,B_150) = B_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1032])).

tff(c_36,plain,(
    ! [A_27,C_29,B_28] :
      ( r1_tarski(k2_xboole_0(A_27,C_29),k2_xboole_0(B_28,C_29))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1712,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k2_xboole_0(A_190,B_191),B_191)
      | ~ r1_tarski(A_190,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_36])).

tff(c_1733,plain,(
    ! [A_190,B_191] :
      ( k4_xboole_0(k2_xboole_0(A_190,B_191),B_191) = k1_xboole_0
      | ~ r1_tarski(A_190,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1712,c_20])).

tff(c_1760,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,B_193) = k1_xboole_0
      | ~ r1_tarski(A_192,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1733])).

tff(c_1769,plain,(
    ! [A_13,B_193] :
      ( k4_xboole_0(A_13,B_193) = k1_xboole_0
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1760])).

tff(c_1776,plain,(
    ! [B_193] : k4_xboole_0(k1_xboole_0,B_193) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1769])).

tff(c_66,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1376,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_3') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1355])).

tff(c_1389,plain,
    ( k2_xboole_0('#skF_3',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_24])).

tff(c_1520,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1389])).

tff(c_1524,plain,(
    k4_xboole_0('#skF_3',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_1520])).

tff(c_69,plain,(
    ! [A_20,B_21] : k2_xboole_0(k4_xboole_0(A_20,B_21),k4_xboole_0(B_21,A_20)) = k5_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_1380,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0('#skF_3',k1_relat_1('#skF_2'))) = k5_xboole_0(k1_relat_1('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_69])).

tff(c_613,plain,(
    ! [A_126,C_127,B_128] :
      ( r1_tarski(k2_xboole_0(A_126,C_127),k2_xboole_0(B_128,C_127))
      | ~ r1_tarski(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2397,plain,(
    ! [A_213,C_214,B_215] :
      ( k4_xboole_0(k2_xboole_0(A_213,C_214),k2_xboole_0(B_215,C_214)) = k1_xboole_0
      | ~ r1_tarski(A_213,B_215) ) ),
    inference(resolution,[status(thm)],[c_613,c_20])).

tff(c_3979,plain,(
    ! [B_257,B_258] :
      ( k4_xboole_0(B_257,k2_xboole_0(B_258,B_257)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_2397])).

tff(c_1403,plain,(
    ! [A_169,A_13] :
      ( k4_xboole_0(A_169,A_13) = A_169
      | k1_xboole_0 != A_13 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_1399])).

tff(c_4339,plain,(
    ! [B_267,B_268] :
      ( k1_xboole_0 = B_267
      | k2_xboole_0(B_268,B_267) != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3979,c_1403])).

tff(c_4351,plain,
    ( k4_xboole_0('#skF_3',k1_relat_1('#skF_2')) = k1_xboole_0
    | k5_xboole_0(k1_relat_1('#skF_2'),'#skF_3') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1380,c_4339])).

tff(c_4363,plain,
    ( k5_xboole_0(k1_relat_1('#skF_2'),'#skF_3') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1524,c_4351])).

tff(c_6897,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4363])).

tff(c_6906,plain,(
    k4_xboole_0(k1_xboole_0,k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_6897])).

tff(c_6912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_6906])).

tff(c_6914,plain,(
    r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4363])).

tff(c_2462,plain,(
    ! [B_14,B_215] :
      ( k4_xboole_0(B_14,k2_xboole_0(B_215,B_14)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_2397])).

tff(c_8382,plain,(
    ! [B_343,A_344] : k2_xboole_0(k4_xboole_0(B_343,k2_xboole_0(A_344,B_343)),k4_xboole_0(A_344,B_343)) = k5_xboole_0(B_343,k2_xboole_0(A_344,B_343)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_661])).

tff(c_8634,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')),k1_relat_1('#skF_2')) = k5_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_8382])).

tff(c_8965,plain,
    ( k5_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) = k2_xboole_0(k1_xboole_0,k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_8634])).

tff(c_9001,plain,(
    k5_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6914,c_1041,c_8965])).

tff(c_137,plain,(
    ! [A_73] :
      ( k1_relat_1(A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_145,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_68,c_137])).

tff(c_146,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_12457,plain,(
    ! [A_391,B_392] : k2_xboole_0(k4_xboole_0(A_391,B_392),k4_xboole_0(B_392,k2_xboole_0(A_391,B_392))) = k5_xboole_0(k2_xboole_0(A_391,B_392),B_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_661])).

tff(c_12748,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'))) = k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_12457])).

tff(c_13478,plain,
    ( k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'),'#skF_3') = k2_xboole_0(k1_relat_1('#skF_2'),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_12748])).

tff(c_13527,plain,(
    k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'),'#skF_3') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6914,c_236,c_13478])).

tff(c_13532,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'))) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13527,c_12748])).

tff(c_1778,plain,(
    ! [A_194,B_195] :
      ( k4_xboole_0(A_194,B_195) = k1_xboole_0
      | k1_xboole_0 != A_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1769])).

tff(c_1810,plain,(
    ! [B_195,A_194] :
      ( k2_xboole_0(k4_xboole_0(B_195,A_194),k1_xboole_0) = k5_xboole_0(B_195,A_194)
      | k1_xboole_0 != A_194 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1778,c_69])).

tff(c_2733,plain,(
    ! [B_220,A_221] :
      ( k5_xboole_0(B_220,A_221) = k4_xboole_0(B_220,A_221)
      | k1_xboole_0 != A_221 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_1810])).

tff(c_356,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_tarski(A_102,k2_xboole_0(B_103,C_104))
      | ~ r1_tarski(A_102,k5_xboole_0(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_371,plain,(
    ! [B_103,C_104] : r1_tarski(k5_xboole_0(B_103,C_104),k2_xboole_0(B_103,C_104)) ),
    inference(resolution,[status(thm)],[c_190,c_356])).

tff(c_6253,plain,(
    ! [B_301,A_302] :
      ( r1_tarski(k4_xboole_0(B_301,A_302),k2_xboole_0(B_301,A_302))
      | k1_xboole_0 != A_302 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2733,c_371])).

tff(c_7683,plain,(
    ! [A_331,A_332] :
      ( r1_tarski(A_331,k2_xboole_0(A_331,A_332))
      | k1_xboole_0 != A_332
      | k1_xboole_0 != A_332 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_6253])).

tff(c_5252,plain,(
    ! [A_284,B_285,A_286] :
      ( r1_tarski(k2_xboole_0(A_284,k4_xboole_0(B_285,A_286)),B_285)
      | ~ r1_tarski(A_284,A_286)
      | ~ r1_tarski(A_286,B_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_613])).

tff(c_232,plain,(
    ! [A_19] :
      ( k2_xboole_0(A_19,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_211])).

tff(c_281,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_232])).

tff(c_5282,plain,(
    ! [A_284,A_286] :
      ( k2_xboole_0(A_284,k4_xboole_0(k1_xboole_0,A_286)) = k1_xboole_0
      | ~ r1_tarski(A_284,A_286)
      | ~ r1_tarski(A_286,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5252,c_281])).

tff(c_5385,plain,(
    ! [A_284,A_286] :
      ( k1_xboole_0 = A_284
      | ~ r1_tarski(A_284,A_286)
      | ~ r1_tarski(A_286,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_1776,c_5282])).

tff(c_7751,plain,(
    ! [A_331,A_332] :
      ( k1_xboole_0 = A_331
      | ~ r1_tarski(k2_xboole_0(A_331,A_332),k1_xboole_0)
      | k1_xboole_0 != A_332 ) ),
    inference(resolution,[status(thm)],[c_7683,c_5385])).

tff(c_15146,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
    | k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13532,c_7751])).

tff(c_15326,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
    | k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_15146])).

tff(c_16319,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15326])).

tff(c_16438,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_16319])).

tff(c_16463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6914,c_16438])).

tff(c_16465,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_15326])).

tff(c_262,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_16])).

tff(c_271,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_262])).

tff(c_16870,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16465,c_271])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_xboole_0(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,k5_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16912,plain,(
    ! [A_8] :
      ( r1_xboole_0(A_8,'#skF_3')
      | ~ r1_tarski(A_8,k5_xboole_0('#skF_3',k2_xboole_0(k1_relat_1('#skF_2'),'#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16870,c_12])).

tff(c_16952,plain,(
    ! [A_417] :
      ( r1_xboole_0(A_417,'#skF_3')
      | ~ r1_tarski(A_417,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9001,c_16912])).

tff(c_17007,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_16952])).

tff(c_56,plain,(
    ! [B_56,A_55] :
      ( k9_relat_1(B_56,A_55) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17160,plain,
    ( k9_relat_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_17007,c_56])).

tff(c_17166,plain,(
    k9_relat_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_17160])).

tff(c_54,plain,(
    ! [B_54,A_53] :
      ( k2_relat_1(k7_relat_1(B_54,A_53)) = k9_relat_1(B_54,A_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k7_relat_1(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_147,plain,(
    ! [A_74] :
      ( k2_relat_1(A_74) != k1_xboole_0
      | k1_xboole_0 = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4335,plain,(
    ! [A_265,B_266] :
      ( k2_relat_1(k7_relat_1(A_265,B_266)) != k1_xboole_0
      | k7_relat_1(A_265,B_266) = k1_xboole_0
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_52,c_147])).

tff(c_34718,plain,(
    ! [B_597,A_598] :
      ( k9_relat_1(B_597,A_598) != k1_xboole_0
      | k7_relat_1(B_597,A_598) = k1_xboole_0
      | ~ v1_relat_1(B_597)
      | ~ v1_relat_1(B_597) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4335])).

tff(c_34722,plain,
    ( k7_relat_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17166,c_34718])).

tff(c_34732,plain,(
    k7_relat_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34722])).

tff(c_34734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_34732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.74/5.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.74/5.86  
% 12.74/5.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.74/5.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.74/5.86  
% 12.74/5.86  %Foreground sorts:
% 12.74/5.86  
% 12.74/5.86  
% 12.74/5.86  %Background operators:
% 12.74/5.86  
% 12.74/5.86  
% 12.74/5.86  %Foreground operators:
% 12.74/5.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.74/5.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.74/5.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.74/5.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.74/5.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.74/5.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.74/5.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.74/5.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.74/5.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.74/5.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.74/5.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.74/5.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.74/5.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.74/5.86  tff('#skF_2', type, '#skF_2': $i).
% 12.74/5.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.74/5.86  tff('#skF_3', type, '#skF_3': $i).
% 12.74/5.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.74/5.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.74/5.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.74/5.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.74/5.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.74/5.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.74/5.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.74/5.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.74/5.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.74/5.86  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.74/5.86  
% 12.97/5.89  tff(f_112, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 12.97/5.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.97/5.89  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 12.97/5.89  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 12.97/5.89  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.97/5.89  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 12.97/5.89  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 12.97/5.89  tff(f_56, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 12.97/5.89  tff(f_64, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.97/5.89  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 12.97/5.89  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 12.97/5.89  tff(f_62, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 12.97/5.89  tff(f_48, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.97/5.89  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 12.97/5.89  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 12.97/5.89  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 12.97/5.89  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 12.97/5.89  tff(f_86, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 12.97/5.89  tff(c_64, plain, (k7_relat_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.97/5.89  tff(c_68, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.97/5.89  tff(c_185, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.97/5.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.97/5.89  tff(c_190, plain, (![A_82]: (r1_tarski(A_82, A_82))), inference(resolution, [status(thm)], [c_185, c_4])).
% 12.97/5.89  tff(c_191, plain, (![A_84]: (r1_tarski(A_84, A_84))), inference(resolution, [status(thm)], [c_185, c_4])).
% 12.97/5.89  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.97/5.89  tff(c_195, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_191, c_20])).
% 12.97/5.89  tff(c_211, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k4_xboole_0(B_87, A_86))=B_87 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.97/5.89  tff(c_226, plain, (![A_84]: (k2_xboole_0(A_84, k1_xboole_0)=A_84 | ~r1_tarski(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_195, c_211])).
% 12.97/5.89  tff(c_236, plain, (![A_84]: (k2_xboole_0(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_226])).
% 12.97/5.89  tff(c_30, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.97/5.89  tff(c_26, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.97/5.89  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), k3_xboole_0(A_6, B_7))=k5_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.97/5.89  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), k3_xboole_0(A_20, B_21))=k2_xboole_0(k4_xboole_0(A_20, B_21), k4_xboole_0(B_21, A_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.97/5.89  tff(c_661, plain, (![A_132, B_133]: (k2_xboole_0(k4_xboole_0(A_132, B_133), k4_xboole_0(B_133, A_132))=k5_xboole_0(A_132, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_28])).
% 12.97/5.89  tff(c_731, plain, (![A_19]: (k2_xboole_0(k4_xboole_0(A_19, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_661])).
% 12.97/5.89  tff(c_742, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_30, c_731])).
% 12.97/5.89  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.97/5.89  tff(c_34, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.97/5.89  tff(c_237, plain, (![A_88]: (k2_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_226])).
% 12.97/5.89  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.97/5.89  tff(c_246, plain, (![A_88]: (k3_xboole_0(A_88, A_88)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_237, c_16])).
% 12.97/5.89  tff(c_426, plain, (![A_110, B_111, C_112]: (r1_xboole_0(A_110, k3_xboole_0(B_111, C_112)) | ~r1_tarski(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.97/5.89  tff(c_432, plain, (![A_110, A_88]: (r1_xboole_0(A_110, A_88) | ~r1_tarski(A_110, k5_xboole_0(A_88, A_88)))), inference(superposition, [status(thm), theory('equality')], [c_246, c_426])).
% 12.97/5.89  tff(c_436, plain, (![A_110, A_88]: (r1_xboole_0(A_110, A_88) | ~r1_tarski(A_110, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_432])).
% 12.97/5.89  tff(c_765, plain, (![A_136]: (k4_xboole_0(A_136, k1_xboole_0)=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_30, c_731])).
% 12.97/5.89  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.97/5.89  tff(c_1017, plain, (![A_145]: (k2_xboole_0(k1_xboole_0, A_145)=A_145 | ~r1_tarski(k1_xboole_0, A_145))), inference(superposition, [status(thm), theory('equality')], [c_765, c_24])).
% 12.97/5.89  tff(c_1032, plain, (![B_14]: (k2_xboole_0(k1_xboole_0, B_14)=B_14 | k4_xboole_0(k1_xboole_0, B_14)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1017])).
% 12.97/5.89  tff(c_1041, plain, (![B_14]: (k2_xboole_0(k1_xboole_0, B_14)=B_14)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1032])).
% 12.97/5.89  tff(c_1181, plain, (![C_153, B_154, A_155]: (k4_xboole_0(k2_xboole_0(C_153, B_154), A_155)=k2_xboole_0(k4_xboole_0(C_153, A_155), B_154) | ~r1_xboole_0(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.97/5.89  tff(c_1226, plain, (![A_155, B_14]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_155), B_14)=k4_xboole_0(B_14, A_155) | ~r1_xboole_0(A_155, B_14))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_1181])).
% 12.97/5.89  tff(c_1355, plain, (![B_167, A_168]: (k4_xboole_0(B_167, A_168)=B_167 | ~r1_xboole_0(A_168, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_26, c_1226])).
% 12.97/5.89  tff(c_1393, plain, (![A_169, A_170]: (k4_xboole_0(A_169, A_170)=A_169 | ~r1_tarski(A_170, k1_xboole_0))), inference(resolution, [status(thm)], [c_436, c_1355])).
% 12.97/5.89  tff(c_1399, plain, (![A_169, A_13]: (k4_xboole_0(A_169, A_13)=A_169 | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1393])).
% 12.97/5.89  tff(c_1404, plain, (![A_169]: (k4_xboole_0(A_169, k1_xboole_0)=A_169)), inference(demodulation, [status(thm), theory('equality')], [c_742, c_1399])).
% 12.97/5.89  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.97/5.89  tff(c_1061, plain, (![B_150]: (k2_xboole_0(k1_xboole_0, B_150)=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1032])).
% 12.97/5.89  tff(c_36, plain, (![A_27, C_29, B_28]: (r1_tarski(k2_xboole_0(A_27, C_29), k2_xboole_0(B_28, C_29)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.97/5.89  tff(c_1712, plain, (![A_190, B_191]: (r1_tarski(k2_xboole_0(A_190, B_191), B_191) | ~r1_tarski(A_190, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1061, c_36])).
% 12.97/5.89  tff(c_1733, plain, (![A_190, B_191]: (k4_xboole_0(k2_xboole_0(A_190, B_191), B_191)=k1_xboole_0 | ~r1_tarski(A_190, k1_xboole_0))), inference(resolution, [status(thm)], [c_1712, c_20])).
% 12.97/5.89  tff(c_1760, plain, (![A_192, B_193]: (k4_xboole_0(A_192, B_193)=k1_xboole_0 | ~r1_tarski(A_192, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1733])).
% 12.97/5.89  tff(c_1769, plain, (![A_13, B_193]: (k4_xboole_0(A_13, B_193)=k1_xboole_0 | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1760])).
% 12.97/5.89  tff(c_1776, plain, (![B_193]: (k4_xboole_0(k1_xboole_0, B_193)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1769])).
% 12.97/5.89  tff(c_66, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.97/5.89  tff(c_1376, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_3')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1355])).
% 12.97/5.89  tff(c_1389, plain, (k2_xboole_0('#skF_3', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2') | ~r1_tarski('#skF_3', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_24])).
% 12.97/5.89  tff(c_1520, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1389])).
% 12.97/5.89  tff(c_1524, plain, (k4_xboole_0('#skF_3', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_1520])).
% 12.97/5.89  tff(c_69, plain, (![A_20, B_21]: (k2_xboole_0(k4_xboole_0(A_20, B_21), k4_xboole_0(B_21, A_20))=k5_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_28])).
% 12.97/5.89  tff(c_1380, plain, (k2_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0('#skF_3', k1_relat_1('#skF_2')))=k5_xboole_0(k1_relat_1('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1376, c_69])).
% 12.97/5.89  tff(c_613, plain, (![A_126, C_127, B_128]: (r1_tarski(k2_xboole_0(A_126, C_127), k2_xboole_0(B_128, C_127)) | ~r1_tarski(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.97/5.89  tff(c_2397, plain, (![A_213, C_214, B_215]: (k4_xboole_0(k2_xboole_0(A_213, C_214), k2_xboole_0(B_215, C_214))=k1_xboole_0 | ~r1_tarski(A_213, B_215))), inference(resolution, [status(thm)], [c_613, c_20])).
% 12.97/5.89  tff(c_3979, plain, (![B_257, B_258]: (k4_xboole_0(B_257, k2_xboole_0(B_258, B_257))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_258))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_2397])).
% 12.97/5.89  tff(c_1403, plain, (![A_169, A_13]: (k4_xboole_0(A_169, A_13)=A_169 | k1_xboole_0!=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_742, c_1399])).
% 12.97/5.89  tff(c_4339, plain, (![B_267, B_268]: (k1_xboole_0=B_267 | k2_xboole_0(B_268, B_267)!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_268))), inference(superposition, [status(thm), theory('equality')], [c_3979, c_1403])).
% 12.97/5.89  tff(c_4351, plain, (k4_xboole_0('#skF_3', k1_relat_1('#skF_2'))=k1_xboole_0 | k5_xboole_0(k1_relat_1('#skF_2'), '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1380, c_4339])).
% 12.97/5.89  tff(c_4363, plain, (k5_xboole_0(k1_relat_1('#skF_2'), '#skF_3')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1524, c_4351])).
% 12.97/5.89  tff(c_6897, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4363])).
% 12.97/5.89  tff(c_6906, plain, (k4_xboole_0(k1_xboole_0, k1_relat_1('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_6897])).
% 12.97/5.89  tff(c_6912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1776, c_6906])).
% 12.97/5.89  tff(c_6914, plain, (r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4363])).
% 12.97/5.89  tff(c_2462, plain, (![B_14, B_215]: (k4_xboole_0(B_14, k2_xboole_0(B_215, B_14))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_215))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_2397])).
% 12.97/5.89  tff(c_8382, plain, (![B_343, A_344]: (k2_xboole_0(k4_xboole_0(B_343, k2_xboole_0(A_344, B_343)), k4_xboole_0(A_344, B_343))=k5_xboole_0(B_343, k2_xboole_0(A_344, B_343)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_661])).
% 12.97/5.89  tff(c_8634, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3')), k1_relat_1('#skF_2'))=k5_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_8382])).
% 12.97/5.89  tff(c_8965, plain, (k5_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))=k2_xboole_0(k1_xboole_0, k1_relat_1('#skF_2')) | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2462, c_8634])).
% 12.97/5.89  tff(c_9001, plain, (k5_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6914, c_1041, c_8965])).
% 12.97/5.89  tff(c_137, plain, (![A_73]: (k1_relat_1(A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.97/5.89  tff(c_145, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_68, c_137])).
% 12.97/5.89  tff(c_146, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_145])).
% 12.97/5.89  tff(c_12457, plain, (![A_391, B_392]: (k2_xboole_0(k4_xboole_0(A_391, B_392), k4_xboole_0(B_392, k2_xboole_0(A_391, B_392)))=k5_xboole_0(k2_xboole_0(A_391, B_392), B_392))), inference(superposition, [status(thm), theory('equality')], [c_22, c_661])).
% 12.97/5.89  tff(c_12748, plain, (k2_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3')))=k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1376, c_12457])).
% 12.97/5.89  tff(c_13478, plain, (k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'), '#skF_3')=k2_xboole_0(k1_relat_1('#skF_2'), k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2462, c_12748])).
% 12.97/5.89  tff(c_13527, plain, (k5_xboole_0(k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'), '#skF_3')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6914, c_236, c_13478])).
% 12.97/5.89  tff(c_13532, plain, (k2_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3')))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13527, c_12748])).
% 12.97/5.89  tff(c_1778, plain, (![A_194, B_195]: (k4_xboole_0(A_194, B_195)=k1_xboole_0 | k1_xboole_0!=A_194)), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1769])).
% 12.97/5.89  tff(c_1810, plain, (![B_195, A_194]: (k2_xboole_0(k4_xboole_0(B_195, A_194), k1_xboole_0)=k5_xboole_0(B_195, A_194) | k1_xboole_0!=A_194)), inference(superposition, [status(thm), theory('equality')], [c_1778, c_69])).
% 12.97/5.89  tff(c_2733, plain, (![B_220, A_221]: (k5_xboole_0(B_220, A_221)=k4_xboole_0(B_220, A_221) | k1_xboole_0!=A_221)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_1810])).
% 12.97/5.89  tff(c_356, plain, (![A_102, B_103, C_104]: (r1_tarski(A_102, k2_xboole_0(B_103, C_104)) | ~r1_tarski(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.97/5.89  tff(c_371, plain, (![B_103, C_104]: (r1_tarski(k5_xboole_0(B_103, C_104), k2_xboole_0(B_103, C_104)))), inference(resolution, [status(thm)], [c_190, c_356])).
% 12.97/5.89  tff(c_6253, plain, (![B_301, A_302]: (r1_tarski(k4_xboole_0(B_301, A_302), k2_xboole_0(B_301, A_302)) | k1_xboole_0!=A_302)), inference(superposition, [status(thm), theory('equality')], [c_2733, c_371])).
% 12.97/5.89  tff(c_7683, plain, (![A_331, A_332]: (r1_tarski(A_331, k2_xboole_0(A_331, A_332)) | k1_xboole_0!=A_332 | k1_xboole_0!=A_332)), inference(superposition, [status(thm), theory('equality')], [c_1403, c_6253])).
% 12.97/5.89  tff(c_5252, plain, (![A_284, B_285, A_286]: (r1_tarski(k2_xboole_0(A_284, k4_xboole_0(B_285, A_286)), B_285) | ~r1_tarski(A_284, A_286) | ~r1_tarski(A_286, B_285))), inference(superposition, [status(thm), theory('equality')], [c_24, c_613])).
% 12.97/5.89  tff(c_232, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_211])).
% 12.97/5.89  tff(c_281, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_232])).
% 12.97/5.89  tff(c_5282, plain, (![A_284, A_286]: (k2_xboole_0(A_284, k4_xboole_0(k1_xboole_0, A_286))=k1_xboole_0 | ~r1_tarski(A_284, A_286) | ~r1_tarski(A_286, k1_xboole_0))), inference(resolution, [status(thm)], [c_5252, c_281])).
% 12.97/5.89  tff(c_5385, plain, (![A_284, A_286]: (k1_xboole_0=A_284 | ~r1_tarski(A_284, A_286) | ~r1_tarski(A_286, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_1776, c_5282])).
% 12.97/5.89  tff(c_7751, plain, (![A_331, A_332]: (k1_xboole_0=A_331 | ~r1_tarski(k2_xboole_0(A_331, A_332), k1_xboole_0) | k1_xboole_0!=A_332)), inference(resolution, [status(thm)], [c_7683, c_5385])).
% 12.97/5.89  tff(c_15146, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13532, c_7751])).
% 12.97/5.89  tff(c_15326, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_146, c_15146])).
% 12.97/5.89  tff(c_16319, plain, (k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15326])).
% 12.97/5.89  tff(c_16438, plain, (~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2462, c_16319])).
% 12.97/5.89  tff(c_16463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6914, c_16438])).
% 12.97/5.89  tff(c_16465, plain, (k4_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_15326])).
% 12.97/5.89  tff(c_262, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=A_90 | ~r1_tarski(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_211, c_16])).
% 12.97/5.89  tff(c_271, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_262])).
% 12.97/5.89  tff(c_16870, plain, (k3_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16465, c_271])).
% 12.97/5.89  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_xboole_0(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.97/5.89  tff(c_16912, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_3') | ~r1_tarski(A_8, k5_xboole_0('#skF_3', k2_xboole_0(k1_relat_1('#skF_2'), '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_16870, c_12])).
% 12.97/5.89  tff(c_16952, plain, (![A_417]: (r1_xboole_0(A_417, '#skF_3') | ~r1_tarski(A_417, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9001, c_16912])).
% 12.97/5.89  tff(c_17007, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_190, c_16952])).
% 12.97/5.89  tff(c_56, plain, (![B_56, A_55]: (k9_relat_1(B_56, A_55)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.97/5.89  tff(c_17160, plain, (k9_relat_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_17007, c_56])).
% 12.97/5.89  tff(c_17166, plain, (k9_relat_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_17160])).
% 12.97/5.89  tff(c_54, plain, (![B_54, A_53]: (k2_relat_1(k7_relat_1(B_54, A_53))=k9_relat_1(B_54, A_53) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.97/5.89  tff(c_52, plain, (![A_51, B_52]: (v1_relat_1(k7_relat_1(A_51, B_52)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.97/5.89  tff(c_147, plain, (![A_74]: (k2_relat_1(A_74)!=k1_xboole_0 | k1_xboole_0=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.97/5.89  tff(c_4335, plain, (![A_265, B_266]: (k2_relat_1(k7_relat_1(A_265, B_266))!=k1_xboole_0 | k7_relat_1(A_265, B_266)=k1_xboole_0 | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_52, c_147])).
% 12.97/5.89  tff(c_34718, plain, (![B_597, A_598]: (k9_relat_1(B_597, A_598)!=k1_xboole_0 | k7_relat_1(B_597, A_598)=k1_xboole_0 | ~v1_relat_1(B_597) | ~v1_relat_1(B_597))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4335])).
% 12.97/5.89  tff(c_34722, plain, (k7_relat_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17166, c_34718])).
% 12.97/5.89  tff(c_34732, plain, (k7_relat_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34722])).
% 12.97/5.89  tff(c_34734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_34732])).
% 12.97/5.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.97/5.89  
% 12.97/5.89  Inference rules
% 12.97/5.89  ----------------------
% 12.97/5.89  #Ref     : 1
% 12.97/5.89  #Sup     : 9057
% 12.97/5.89  #Fact    : 0
% 12.97/5.89  #Define  : 0
% 12.97/5.89  #Split   : 9
% 12.97/5.89  #Chain   : 0
% 12.97/5.89  #Close   : 0
% 12.97/5.89  
% 12.97/5.89  Ordering : KBO
% 12.97/5.89  
% 12.97/5.89  Simplification rules
% 12.97/5.89  ----------------------
% 12.97/5.89  #Subsume      : 2626
% 12.97/5.89  #Demod        : 5179
% 12.97/5.89  #Tautology    : 2281
% 12.97/5.89  #SimpNegUnit  : 292
% 12.97/5.89  #BackRed      : 84
% 12.97/5.89  
% 12.97/5.89  #Partial instantiations: 0
% 12.97/5.89  #Strategies tried      : 1
% 12.97/5.89  
% 12.97/5.89  Timing (in seconds)
% 12.97/5.89  ----------------------
% 12.97/5.89  Preprocessing        : 0.34
% 12.97/5.89  Parsing              : 0.19
% 12.97/5.89  CNF conversion       : 0.02
% 12.97/5.89  Main loop            : 4.73
% 12.97/5.89  Inferencing          : 0.91
% 12.97/5.89  Reduction            : 2.16
% 12.97/5.89  Demodulation         : 1.76
% 12.97/5.89  BG Simplification    : 0.13
% 12.97/5.89  Subsumption          : 1.28
% 12.97/5.89  Abstraction          : 0.18
% 12.97/5.89  MUC search           : 0.00
% 12.97/5.89  Cooper               : 0.00
% 12.97/5.89  Total                : 5.14
% 12.97/5.89  Index Insertion      : 0.00
% 12.97/5.89  Index Deletion       : 0.00
% 12.97/5.89  Index Matching       : 0.00
% 12.97/5.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
