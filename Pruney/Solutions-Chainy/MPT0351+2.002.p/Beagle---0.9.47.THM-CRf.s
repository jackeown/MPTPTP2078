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
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 262 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :   97 ( 385 expanded)
%              Number of equality atoms :   58 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_450,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_576,plain,(
    ! [A_96,B_97] :
      ( k4_subset_1(A_96,B_97,A_96) = k2_xboole_0(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_48,c_450])).

tff(c_587,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_576])).

tff(c_44,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_44])).

tff(c_643,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_47])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_150,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_146])).

tff(c_296,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_405,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,k4_xboole_0(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_22])).

tff(c_420,plain,(
    ! [B_9] : k3_xboole_0(B_9,k4_xboole_0(B_9,B_9)) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_405])).

tff(c_42,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_401,plain,(
    ! [C_80,A_81,B_82] :
      ( r2_hidden(C_80,A_81)
      | ~ r2_hidden(C_80,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_703,plain,(
    ! [A_104,B_105,A_106] :
      ( r2_hidden('#skF_1'(A_104,B_105),A_106)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(A_106))
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_8,c_401])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_715,plain,(
    ! [A_107,A_108] :
      ( ~ m1_subset_1(A_107,k1_zfmisc_1(A_108))
      | r1_tarski(A_107,A_108) ) ),
    inference(resolution,[status(thm)],[c_703,c_6])).

tff(c_729,plain,(
    ! [A_109] : r1_tarski(k1_xboole_0,A_109) ),
    inference(resolution,[status(thm)],[c_42,c_715])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_744,plain,(
    ! [A_110] : k3_xboole_0(k1_xboole_0,A_110) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_729,c_20])).

tff(c_778,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_744])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_878,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_24])).

tff(c_883,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_878])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_762,plain,(
    ! [A_110] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_16])).

tff(c_1076,plain,(
    ! [A_118] : k4_xboole_0(k1_xboole_0,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_762])).

tff(c_1110,plain,(
    ! [A_118] : k5_xboole_0(A_118,k1_xboole_0) = k2_xboole_0(A_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_24])).

tff(c_1138,plain,(
    ! [A_118] : k5_xboole_0(A_118,k1_xboole_0) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1110])).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_175,plain,(
    ! [B_54,A_55] : k3_tarski(k2_tarski(B_54,A_55)) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_160])).

tff(c_32,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_790,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_744])).

tff(c_329,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_341,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_329])).

tff(c_759,plain,(
    ! [A_110] : k5_xboole_0(A_110,k1_xboole_0) = k4_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_341])).

tff(c_1166,plain,(
    ! [A_120] : k4_xboole_0(A_120,k1_xboole_0) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_759])).

tff(c_411,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k3_xboole_0(A_83,k4_xboole_0(A_83,B_84))) = k3_xboole_0(A_83,k3_xboole_0(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_22])).

tff(c_1179,plain,(
    ! [A_120] : k4_xboole_0(A_120,k3_xboole_0(A_120,A_120)) = k3_xboole_0(A_120,k3_xboole_0(A_120,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_411])).

tff(c_1200,plain,(
    ! [A_120] : k4_xboole_0(A_120,A_120) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_790,c_150,c_1179])).

tff(c_338,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_329])).

tff(c_728,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_715])).

tff(c_743,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_728,c_20])).

tff(c_808,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_16])).

tff(c_811,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_808])).

tff(c_1206,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_811])).

tff(c_1313,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_24])).

tff(c_1319,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_181,c_1313])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_1319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.48  
% 3.04/1.48  %Foreground sorts:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Background operators:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Foreground operators:
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.04/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.04/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.48  
% 3.04/1.49  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.04/1.49  tff(f_62, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.04/1.49  tff(f_64, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.04/1.49  tff(f_77, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.04/1.49  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.04/1.49  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.49  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.49  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.04/1.49  tff(f_79, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.04/1.49  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.49  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.04/1.49  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.04/1.49  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.04/1.49  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.04/1.49  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.04/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.04/1.49  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.49  tff(c_34, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.04/1.49  tff(c_36, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.04/1.49  tff(c_48, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.04/1.49  tff(c_450, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.49  tff(c_576, plain, (![A_96, B_97]: (k4_subset_1(A_96, B_97, A_96)=k2_xboole_0(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_48, c_450])).
% 3.04/1.49  tff(c_587, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_576])).
% 3.04/1.49  tff(c_44, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.49  tff(c_47, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_44])).
% 3.04/1.49  tff(c_643, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_47])).
% 3.04/1.49  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.49  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.04/1.49  tff(c_146, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.04/1.49  tff(c_150, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_146])).
% 3.04/1.49  tff(c_296, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.04/1.49  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.04/1.49  tff(c_405, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k3_xboole_0(A_83, k4_xboole_0(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_22])).
% 3.04/1.49  tff(c_420, plain, (![B_9]: (k3_xboole_0(B_9, k4_xboole_0(B_9, B_9))=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_150, c_405])).
% 3.04/1.50  tff(c_42, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.04/1.50  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.50  tff(c_401, plain, (![C_80, A_81, B_82]: (r2_hidden(C_80, A_81) | ~r2_hidden(C_80, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.50  tff(c_703, plain, (![A_104, B_105, A_106]: (r2_hidden('#skF_1'(A_104, B_105), A_106) | ~m1_subset_1(A_104, k1_zfmisc_1(A_106)) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_8, c_401])).
% 3.04/1.50  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.50  tff(c_715, plain, (![A_107, A_108]: (~m1_subset_1(A_107, k1_zfmisc_1(A_108)) | r1_tarski(A_107, A_108))), inference(resolution, [status(thm)], [c_703, c_6])).
% 3.04/1.50  tff(c_729, plain, (![A_109]: (r1_tarski(k1_xboole_0, A_109))), inference(resolution, [status(thm)], [c_42, c_715])).
% 3.04/1.50  tff(c_20, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.04/1.50  tff(c_744, plain, (![A_110]: (k3_xboole_0(k1_xboole_0, A_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_729, c_20])).
% 3.04/1.50  tff(c_778, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_420, c_744])).
% 3.04/1.50  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.50  tff(c_878, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_778, c_24])).
% 3.04/1.50  tff(c_883, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_878])).
% 3.04/1.50  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.50  tff(c_762, plain, (![A_110]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_110))), inference(superposition, [status(thm), theory('equality')], [c_744, c_16])).
% 3.04/1.50  tff(c_1076, plain, (![A_118]: (k4_xboole_0(k1_xboole_0, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_883, c_762])).
% 3.04/1.50  tff(c_1110, plain, (![A_118]: (k5_xboole_0(A_118, k1_xboole_0)=k2_xboole_0(A_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1076, c_24])).
% 3.04/1.50  tff(c_1138, plain, (![A_118]: (k5_xboole_0(A_118, k1_xboole_0)=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1110])).
% 3.04/1.50  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.04/1.50  tff(c_160, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.04/1.50  tff(c_175, plain, (![B_54, A_55]: (k3_tarski(k2_tarski(B_54, A_55))=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_26, c_160])).
% 3.04/1.50  tff(c_32, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.04/1.50  tff(c_181, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_175, c_32])).
% 3.04/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.04/1.50  tff(c_790, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_744])).
% 3.04/1.50  tff(c_329, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.50  tff(c_341, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_329])).
% 3.04/1.50  tff(c_759, plain, (![A_110]: (k5_xboole_0(A_110, k1_xboole_0)=k4_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_744, c_341])).
% 3.04/1.50  tff(c_1166, plain, (![A_120]: (k4_xboole_0(A_120, k1_xboole_0)=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_759])).
% 3.04/1.50  tff(c_411, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k3_xboole_0(A_83, k4_xboole_0(A_83, B_84)))=k3_xboole_0(A_83, k3_xboole_0(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_405, c_22])).
% 3.04/1.50  tff(c_1179, plain, (![A_120]: (k4_xboole_0(A_120, k3_xboole_0(A_120, A_120))=k3_xboole_0(A_120, k3_xboole_0(A_120, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_411])).
% 3.04/1.50  tff(c_1200, plain, (![A_120]: (k4_xboole_0(A_120, A_120)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_790, c_790, c_150, c_1179])).
% 3.04/1.50  tff(c_338, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_150, c_329])).
% 3.04/1.50  tff(c_728, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_715])).
% 3.04/1.50  tff(c_743, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_728, c_20])).
% 3.04/1.50  tff(c_808, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_743, c_16])).
% 3.04/1.50  tff(c_811, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_808])).
% 3.04/1.50  tff(c_1206, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_811])).
% 3.04/1.50  tff(c_1313, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_24])).
% 3.04/1.50  tff(c_1319, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_181, c_1313])).
% 3.04/1.50  tff(c_1321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_1319])).
% 3.04/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  Inference rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Ref     : 0
% 3.04/1.50  #Sup     : 306
% 3.04/1.50  #Fact    : 0
% 3.04/1.50  #Define  : 0
% 3.04/1.50  #Split   : 1
% 3.04/1.50  #Chain   : 0
% 3.04/1.50  #Close   : 0
% 3.04/1.50  
% 3.04/1.50  Ordering : KBO
% 3.04/1.50  
% 3.04/1.50  Simplification rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Subsume      : 1
% 3.04/1.50  #Demod        : 197
% 3.04/1.50  #Tautology    : 230
% 3.04/1.50  #SimpNegUnit  : 1
% 3.04/1.50  #BackRed      : 5
% 3.04/1.50  
% 3.04/1.50  #Partial instantiations: 0
% 3.04/1.50  #Strategies tried      : 1
% 3.04/1.50  
% 3.04/1.50  Timing (in seconds)
% 3.04/1.50  ----------------------
% 3.04/1.50  Preprocessing        : 0.31
% 3.04/1.50  Parsing              : 0.17
% 3.04/1.50  CNF conversion       : 0.02
% 3.04/1.50  Main loop            : 0.41
% 3.04/1.50  Inferencing          : 0.14
% 3.04/1.50  Reduction            : 0.16
% 3.04/1.50  Demodulation         : 0.12
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.07
% 3.19/1.50  Abstraction          : 0.02
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.76
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
