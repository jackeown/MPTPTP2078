%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 692 expanded)
%              Number of leaves         :   42 ( 253 expanded)
%              Depth                    :   22
%              Number of atoms          :  111 ( 690 expanded)
%              Number of equality atoms :   79 ( 652 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_70,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_54] : k2_subset_1(A_54) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_55] : m1_subset_1(k2_subset_1(A_55),k1_zfmisc_1(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [A_55] : m1_subset_1(A_55,k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_1082,plain,(
    ! [A_138,B_139,C_140] :
      ( k4_subset_1(A_138,B_139,C_140) = k2_xboole_0(B_139,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(A_138))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4049,plain,(
    ! [A_216,B_217] :
      ( k4_subset_1(A_216,B_217,A_216) = k2_xboole_0(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(resolution,[status(thm)],[c_53,c_1082])).

tff(c_4056,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_4049])).

tff(c_50,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_50])).

tff(c_4066,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4056,c_54])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_506,plain,(
    ! [C_104,A_105,B_106] :
      ( r2_hidden(C_104,A_105)
      | ~ r2_hidden(C_104,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4944,plain,(
    ! [A_234,B_235,A_236] :
      ( r2_hidden('#skF_1'(A_234,B_235),A_236)
      | ~ m1_subset_1(A_234,k1_zfmisc_1(A_236))
      | r1_tarski(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_8,c_506])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4956,plain,(
    ! [A_237,A_238] :
      ( ~ m1_subset_1(A_237,k1_zfmisc_1(A_238))
      | r1_tarski(A_237,A_238) ) ),
    inference(resolution,[status(thm)],[c_4944,c_6])).

tff(c_4965,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_4956])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4969,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4965,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_510,plain,(
    ! [A_107,B_108] : k5_xboole_0(k5_xboole_0(A_107,B_108),k3_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_546,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_510])).

tff(c_636,plain,(
    ! [A_112] : k2_xboole_0(A_112,k1_xboole_0) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_546])).

tff(c_26,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_235,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_251,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_235])).

tff(c_40,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_257,plain,(
    ! [B_80,A_79] : k2_xboole_0(B_80,A_79) = k2_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_40])).

tff(c_642,plain,(
    ! [A_112] : k2_xboole_0(k1_xboole_0,A_112) = A_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_257])).

tff(c_133,plain,(
    ! [B_70,A_71] : k3_xboole_0(B_70,A_71) = k3_xboole_0(A_71,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_71] : k3_xboole_0(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_16])).

tff(c_324,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_345,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_324])).

tff(c_350,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_345])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_356,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k3_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_18])).

tff(c_361,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_356])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_342,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_324])).

tff(c_435,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_342])).

tff(c_543,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_510])).

tff(c_709,plain,(
    ! [A_118] : k5_xboole_0(k1_xboole_0,A_118) = k2_xboole_0(A_118,A_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_543])).

tff(c_24,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_721,plain,(
    ! [A_118] : k5_xboole_0(k2_xboole_0(A_118,A_118),k3_xboole_0(k1_xboole_0,A_118)) = k2_xboole_0(k1_xboole_0,A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_24])).

tff(c_745,plain,(
    ! [A_118] : k2_xboole_0(A_118,A_118) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_20,c_149,c_721])).

tff(c_555,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = k2_xboole_0(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_543])).

tff(c_751,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_555])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_558,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_609,plain,(
    ! [A_8,C_111] : k5_xboole_0(A_8,k5_xboole_0(A_8,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_558])).

tff(c_910,plain,(
    ! [A_134,C_135] : k5_xboole_0(A_134,k5_xboole_0(A_134,C_135)) = C_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_609])).

tff(c_1639,plain,(
    ! [A_159,B_160] : k5_xboole_0(A_159,k4_xboole_0(A_159,B_160)) = k3_xboole_0(A_159,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_910])).

tff(c_1705,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1639])).

tff(c_2239,plain,(
    ! [A_173,B_174] : k3_xboole_0(A_173,k4_xboole_0(A_173,B_174)) = k4_xboole_0(A_173,B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1705])).

tff(c_336,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_324])).

tff(c_2257,plain,(
    ! [A_173,B_174] : k5_xboole_0(k4_xboole_0(A_173,B_174),k4_xboole_0(A_173,B_174)) = k4_xboole_0(k4_xboole_0(A_173,B_174),A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_2239,c_336])).

tff(c_2343,plain,(
    ! [A_177,B_178] : k4_xboole_0(k4_xboole_0(A_177,B_178),A_177) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_2257])).

tff(c_2400,plain,(
    ! [A_15,B_16] : k4_xboole_0(k3_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2343])).

tff(c_571,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k5_xboole_0(B_110,k3_xboole_0(A_109,B_110))) = k2_xboole_0(A_109,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_24])).

tff(c_630,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k2_xboole_0(A_109,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_571])).

tff(c_1717,plain,(
    ! [A_161,B_162] : k5_xboole_0(A_161,k2_xboole_0(A_161,B_162)) = k4_xboole_0(B_162,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_910])).

tff(c_2158,plain,(
    ! [B_171,A_172] : k5_xboole_0(B_171,k2_xboole_0(A_172,B_171)) = k4_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_1717])).

tff(c_981,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k5_xboole_0(B_137,k5_xboole_0(A_136,B_137))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_558])).

tff(c_909,plain,(
    ! [A_8,C_111] : k5_xboole_0(A_8,k5_xboole_0(A_8,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_609])).

tff(c_989,plain,(
    ! [B_137,A_136] : k5_xboole_0(B_137,k5_xboole_0(A_136,B_137)) = k5_xboole_0(A_136,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_909])).

tff(c_1091,plain,(
    ! [B_141,A_142] : k5_xboole_0(B_141,k5_xboole_0(A_142,B_141)) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_989])).

tff(c_1066,plain,(
    ! [B_137,A_136] : k5_xboole_0(B_137,k5_xboole_0(A_136,B_137)) = A_136 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_989])).

tff(c_1094,plain,(
    ! [A_142,B_141] : k5_xboole_0(k5_xboole_0(A_142,B_141),A_142) = B_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_1066])).

tff(c_4524,plain,(
    ! [A_226,B_227] : k5_xboole_0(k4_xboole_0(A_226,B_227),B_227) = k2_xboole_0(A_226,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_1094])).

tff(c_4595,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),A_15) = k5_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_4524])).

tff(c_4740,plain,(
    ! [A_230,B_231] : k2_xboole_0(k3_xboole_0(A_230,B_231),A_230) = A_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_4595])).

tff(c_4807,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4740])).

tff(c_4973,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4969,c_4807])).

tff(c_5040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4066,c_4973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.03  
% 5.07/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.04  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.07/2.04  
% 5.07/2.04  %Foreground sorts:
% 5.07/2.04  
% 5.07/2.04  
% 5.07/2.04  %Background operators:
% 5.07/2.04  
% 5.07/2.04  
% 5.07/2.04  %Foreground operators:
% 5.07/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.07/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/2.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.07/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.07/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.07/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.07/2.04  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.07/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.07/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.07/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.07/2.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.07/2.04  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.07/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.07/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.07/2.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.07/2.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.07/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.07/2.04  
% 5.46/2.08  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 5.46/2.08  tff(f_70, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.46/2.08  tff(f_72, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.46/2.08  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.46/2.08  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.46/2.08  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.46/2.08  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.46/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.46/2.08  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.46/2.08  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.46/2.08  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.46/2.08  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.46/2.08  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.46/2.08  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.46/2.08  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.46/2.08  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.46/2.08  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.46/2.08  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.46/2.08  tff(c_42, plain, (![A_54]: (k2_subset_1(A_54)=A_54)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.46/2.08  tff(c_44, plain, (![A_55]: (m1_subset_1(k2_subset_1(A_55), k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.46/2.08  tff(c_53, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 5.46/2.08  tff(c_1082, plain, (![A_138, B_139, C_140]: (k4_subset_1(A_138, B_139, C_140)=k2_xboole_0(B_139, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(A_138)) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.46/2.08  tff(c_4049, plain, (![A_216, B_217]: (k4_subset_1(A_216, B_217, A_216)=k2_xboole_0(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(resolution, [status(thm)], [c_53, c_1082])).
% 5.46/2.08  tff(c_4056, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_4049])).
% 5.46/2.08  tff(c_50, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.46/2.08  tff(c_54, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_50])).
% 5.46/2.08  tff(c_4066, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4056, c_54])).
% 5.46/2.08  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.46/2.08  tff(c_506, plain, (![C_104, A_105, B_106]: (r2_hidden(C_104, A_105) | ~r2_hidden(C_104, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.46/2.08  tff(c_4944, plain, (![A_234, B_235, A_236]: (r2_hidden('#skF_1'(A_234, B_235), A_236) | ~m1_subset_1(A_234, k1_zfmisc_1(A_236)) | r1_tarski(A_234, B_235))), inference(resolution, [status(thm)], [c_8, c_506])).
% 5.46/2.08  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.46/2.08  tff(c_4956, plain, (![A_237, A_238]: (~m1_subset_1(A_237, k1_zfmisc_1(A_238)) | r1_tarski(A_237, A_238))), inference(resolution, [status(thm)], [c_4944, c_6])).
% 5.46/2.08  tff(c_4965, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_4956])).
% 5.46/2.08  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.46/2.08  tff(c_4969, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_4965, c_14])).
% 5.46/2.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.46/2.08  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.46/2.08  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.46/2.08  tff(c_510, plain, (![A_107, B_108]: (k5_xboole_0(k5_xboole_0(A_107, B_108), k3_xboole_0(A_107, B_108))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.08  tff(c_546, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_510])).
% 5.46/2.08  tff(c_636, plain, (![A_112]: (k2_xboole_0(A_112, k1_xboole_0)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_546])).
% 5.46/2.08  tff(c_26, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.46/2.08  tff(c_235, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.46/2.08  tff(c_251, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_26, c_235])).
% 5.46/2.08  tff(c_40, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.46/2.08  tff(c_257, plain, (![B_80, A_79]: (k2_xboole_0(B_80, A_79)=k2_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_251, c_40])).
% 5.46/2.08  tff(c_642, plain, (![A_112]: (k2_xboole_0(k1_xboole_0, A_112)=A_112)), inference(superposition, [status(thm), theory('equality')], [c_636, c_257])).
% 5.46/2.08  tff(c_133, plain, (![B_70, A_71]: (k3_xboole_0(B_70, A_71)=k3_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.46/2.08  tff(c_149, plain, (![A_71]: (k3_xboole_0(k1_xboole_0, A_71)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_16])).
% 5.46/2.08  tff(c_324, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.46/2.08  tff(c_345, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_324])).
% 5.46/2.08  tff(c_350, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_345])).
% 5.46/2.08  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.46/2.08  tff(c_356, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k3_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_350, c_18])).
% 5.46/2.08  tff(c_361, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_356])).
% 5.46/2.08  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.46/2.08  tff(c_342, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_324])).
% 5.46/2.08  tff(c_435, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_361, c_342])).
% 5.46/2.08  tff(c_543, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_510])).
% 5.46/2.08  tff(c_709, plain, (![A_118]: (k5_xboole_0(k1_xboole_0, A_118)=k2_xboole_0(A_118, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_543])).
% 5.46/2.08  tff(c_24, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.08  tff(c_721, plain, (![A_118]: (k5_xboole_0(k2_xboole_0(A_118, A_118), k3_xboole_0(k1_xboole_0, A_118))=k2_xboole_0(k1_xboole_0, A_118))), inference(superposition, [status(thm), theory('equality')], [c_709, c_24])).
% 5.46/2.08  tff(c_745, plain, (![A_118]: (k2_xboole_0(A_118, A_118)=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_642, c_20, c_149, c_721])).
% 5.46/2.08  tff(c_555, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=k2_xboole_0(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_543])).
% 5.46/2.08  tff(c_751, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_745, c_555])).
% 5.46/2.08  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.46/2.08  tff(c_558, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.46/2.08  tff(c_609, plain, (![A_8, C_111]: (k5_xboole_0(A_8, k5_xboole_0(A_8, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_435, c_558])).
% 5.46/2.08  tff(c_910, plain, (![A_134, C_135]: (k5_xboole_0(A_134, k5_xboole_0(A_134, C_135))=C_135)), inference(demodulation, [status(thm), theory('equality')], [c_751, c_609])).
% 5.46/2.08  tff(c_1639, plain, (![A_159, B_160]: (k5_xboole_0(A_159, k4_xboole_0(A_159, B_160))=k3_xboole_0(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_12, c_910])).
% 5.46/2.08  tff(c_1705, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1639])).
% 5.46/2.08  tff(c_2239, plain, (![A_173, B_174]: (k3_xboole_0(A_173, k4_xboole_0(A_173, B_174))=k4_xboole_0(A_173, B_174))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1705])).
% 5.46/2.08  tff(c_336, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_324])).
% 5.46/2.08  tff(c_2257, plain, (![A_173, B_174]: (k5_xboole_0(k4_xboole_0(A_173, B_174), k4_xboole_0(A_173, B_174))=k4_xboole_0(k4_xboole_0(A_173, B_174), A_173))), inference(superposition, [status(thm), theory('equality')], [c_2239, c_336])).
% 5.46/2.08  tff(c_2343, plain, (![A_177, B_178]: (k4_xboole_0(k4_xboole_0(A_177, B_178), A_177)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_2257])).
% 5.46/2.08  tff(c_2400, plain, (![A_15, B_16]: (k4_xboole_0(k3_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_2343])).
% 5.46/2.08  tff(c_571, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k5_xboole_0(B_110, k3_xboole_0(A_109, B_110)))=k2_xboole_0(A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_558, c_24])).
% 5.46/2.08  tff(c_630, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k2_xboole_0(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_571])).
% 5.46/2.08  tff(c_1717, plain, (![A_161, B_162]: (k5_xboole_0(A_161, k2_xboole_0(A_161, B_162))=k4_xboole_0(B_162, A_161))), inference(superposition, [status(thm), theory('equality')], [c_630, c_910])).
% 5.46/2.08  tff(c_2158, plain, (![B_171, A_172]: (k5_xboole_0(B_171, k2_xboole_0(A_172, B_171))=k4_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_257, c_1717])).
% 5.46/2.08  tff(c_981, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k5_xboole_0(B_137, k5_xboole_0(A_136, B_137)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_435, c_558])).
% 5.46/2.08  tff(c_909, plain, (![A_8, C_111]: (k5_xboole_0(A_8, k5_xboole_0(A_8, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_751, c_609])).
% 5.46/2.08  tff(c_989, plain, (![B_137, A_136]: (k5_xboole_0(B_137, k5_xboole_0(A_136, B_137))=k5_xboole_0(A_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_981, c_909])).
% 5.46/2.08  tff(c_1091, plain, (![B_141, A_142]: (k5_xboole_0(B_141, k5_xboole_0(A_142, B_141))=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_989])).
% 5.46/2.08  tff(c_1066, plain, (![B_137, A_136]: (k5_xboole_0(B_137, k5_xboole_0(A_136, B_137))=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_989])).
% 5.46/2.08  tff(c_1094, plain, (![A_142, B_141]: (k5_xboole_0(k5_xboole_0(A_142, B_141), A_142)=B_141)), inference(superposition, [status(thm), theory('equality')], [c_1091, c_1066])).
% 5.46/2.08  tff(c_4524, plain, (![A_226, B_227]: (k5_xboole_0(k4_xboole_0(A_226, B_227), B_227)=k2_xboole_0(A_226, B_227))), inference(superposition, [status(thm), theory('equality')], [c_2158, c_1094])).
% 5.46/2.08  tff(c_4595, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), A_15)=k5_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_2400, c_4524])).
% 5.46/2.08  tff(c_4740, plain, (![A_230, B_231]: (k2_xboole_0(k3_xboole_0(A_230, B_231), A_230)=A_230)), inference(demodulation, [status(thm), theory('equality')], [c_751, c_4595])).
% 5.46/2.08  tff(c_4807, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4740])).
% 5.46/2.08  tff(c_4973, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4969, c_4807])).
% 5.46/2.08  tff(c_5040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4066, c_4973])).
% 5.46/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.08  
% 5.46/2.08  Inference rules
% 5.46/2.08  ----------------------
% 5.46/2.08  #Ref     : 0
% 5.46/2.08  #Sup     : 1234
% 5.46/2.08  #Fact    : 0
% 5.46/2.08  #Define  : 0
% 5.46/2.08  #Split   : 0
% 5.46/2.08  #Chain   : 0
% 5.46/2.08  #Close   : 0
% 5.46/2.08  
% 5.46/2.08  Ordering : KBO
% 5.46/2.08  
% 5.46/2.08  Simplification rules
% 5.46/2.08  ----------------------
% 5.46/2.08  #Subsume      : 28
% 5.46/2.08  #Demod        : 1193
% 5.46/2.08  #Tautology    : 856
% 5.46/2.08  #SimpNegUnit  : 1
% 5.46/2.08  #BackRed      : 3
% 5.46/2.08  
% 5.46/2.08  #Partial instantiations: 0
% 5.46/2.08  #Strategies tried      : 1
% 5.46/2.08  
% 5.46/2.08  Timing (in seconds)
% 5.46/2.08  ----------------------
% 5.46/2.09  Preprocessing        : 0.33
% 5.46/2.09  Parsing              : 0.18
% 5.46/2.09  CNF conversion       : 0.02
% 5.46/2.09  Main loop            : 0.94
% 5.46/2.09  Inferencing          : 0.30
% 5.46/2.09  Reduction            : 0.43
% 5.46/2.09  Demodulation         : 0.36
% 5.46/2.09  BG Simplification    : 0.04
% 5.46/2.09  Subsumption          : 0.12
% 5.46/2.09  Abstraction          : 0.05
% 5.58/2.09  MUC search           : 0.00
% 5.58/2.09  Cooper               : 0.00
% 5.58/2.09  Total                : 1.34
% 5.58/2.09  Index Insertion      : 0.00
% 5.58/2.09  Index Deletion       : 0.00
% 5.58/2.09  Index Matching       : 0.00
% 5.58/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
