%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 318 expanded)
%              Number of leaves         :   40 ( 122 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 402 expanded)
%              Number of equality atoms :   85 ( 239 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_242,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_246,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_242])).

tff(c_30,plain,(
    ! [A_27] : k1_subset_1(A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_subset_1(A_34)) = k2_subset_1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_subset_1(A_34)) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_61,plain,(
    ! [A_34] : k3_subset_1(A_34,k1_xboole_0) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_46,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_827,plain,(
    ! [A_91,B_92] :
      ( k3_subset_1(A_91,k3_subset_1(A_91,B_92)) = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_829,plain,(
    ! [A_39] : k3_subset_1(A_39,k3_subset_1(A_39,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_827])).

tff(c_833,plain,(
    ! [A_39] : k3_subset_1(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_829])).

tff(c_359,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,B_69)
      | k4_xboole_0(A_68,B_69) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_138,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56])).

tff(c_269,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_59])).

tff(c_270,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_269,c_138])).

tff(c_370,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_1'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_359,c_270])).

tff(c_835,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_370])).

tff(c_839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_835])).

tff(c_840,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_31] : m1_subset_1(k2_subset_1(A_31),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_31] : m1_subset_1(A_31,k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_1671,plain,(
    ! [A_134,B_135] :
      ( k3_subset_1(A_134,k3_subset_1(A_134,B_135)) = B_135
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1675,plain,(
    ! [A_39] : k3_subset_1(A_39,k3_subset_1(A_39,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1671])).

tff(c_1680,plain,(
    ! [A_39] : k3_subset_1(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1675])).

tff(c_1894,plain,(
    ! [B_145,C_146,A_147] :
      ( r1_tarski(B_145,C_146)
      | ~ r1_tarski(k3_subset_1(A_147,C_146),k3_subset_1(A_147,B_145))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1903,plain,(
    ! [B_145,A_39] :
      ( r1_tarski(B_145,A_39)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_39,B_145))
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_1894])).

tff(c_1925,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16,c_1903])).

tff(c_1935,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1925])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1945,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1935,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_1973,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1945,c_135])).

tff(c_22,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_947,plain,(
    ! [A_101,B_102] : k3_tarski(k2_tarski(A_101,B_102)) = k2_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1081,plain,(
    ! [B_113,A_114] : k3_tarski(k2_tarski(B_113,A_114)) = k2_xboole_0(A_114,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_947])).

tff(c_28,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1087,plain,(
    ! [B_113,A_114] : k2_xboole_0(B_113,A_114) = k2_xboole_0(A_114,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_28])).

tff(c_1764,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(A_139,B_140) = k3_subset_1(A_139,B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1774,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1764])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1782,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_20])).

tff(c_1788,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1782])).

tff(c_2012,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1788])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_982,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_991,plain,(
    ! [A_108] : k3_xboole_0(k1_xboole_0,A_108) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_982])).

tff(c_996,plain,(
    ! [A_108] : k2_xboole_0(A_108,k1_xboole_0) = A_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_135])).

tff(c_938,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k1_xboole_0
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_946,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_938])).

tff(c_1404,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k4_xboole_0(B_125,A_124)) = k2_xboole_0(A_124,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1427,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_1404])).

tff(c_1434,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_1427])).

tff(c_1005,plain,(
    ! [A_108] : k3_xboole_0(A_108,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_2])).

tff(c_1233,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1245,plain,(
    ! [A_108] : k5_xboole_0(A_108,k1_xboole_0) = k4_xboole_0(A_108,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1233])).

tff(c_1435,plain,(
    ! [A_108] : k4_xboole_0(A_108,k1_xboole_0) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1434,c_1245])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1946,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1935,c_8])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2004,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1946,c_18])).

tff(c_2010,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_2,c_2004])).

tff(c_841,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_989,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_841,c_982])).

tff(c_1123,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_989])).

tff(c_1803,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k3_xboole_0(B_142,A_141)) = k4_xboole_0(A_141,B_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1233])).

tff(c_1834,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_1803])).

tff(c_2722,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_1834])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1370,plain,(
    ! [A_122,B_123] : k4_xboole_0(A_122,k4_xboole_0(A_122,B_123)) = k3_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2181,plain,(
    ! [A_156,B_157] : k4_xboole_0(A_156,k3_xboole_0(A_156,B_157)) = k3_xboole_0(A_156,k4_xboole_0(A_156,B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1370])).

tff(c_2190,plain,(
    ! [A_156,B_157] : k5_xboole_0(k3_xboole_0(A_156,B_157),k3_xboole_0(A_156,k4_xboole_0(A_156,B_157))) = k2_xboole_0(k3_xboole_0(A_156,B_157),A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2181,c_20])).

tff(c_2236,plain,(
    ! [A_156,B_157] : k5_xboole_0(k3_xboole_0(A_156,B_157),k3_xboole_0(A_156,k4_xboole_0(A_156,B_157))) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1087,c_2190])).

tff(c_2729,plain,(
    k5_xboole_0(k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')),k3_xboole_0('#skF_2','#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2722,c_2236])).

tff(c_2749,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_4,c_2010,c_4,c_1123,c_4,c_2,c_2729])).

tff(c_2751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_2749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:10:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.75  
% 3.87/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.75  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.87/1.75  
% 3.87/1.75  %Foreground sorts:
% 3.87/1.75  
% 3.87/1.75  
% 3.87/1.75  %Background operators:
% 3.87/1.75  
% 3.87/1.75  
% 3.87/1.75  %Foreground operators:
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.87/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.87/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.87/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.87/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.75  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.87/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.87/1.75  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.87/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.75  
% 3.87/1.77  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.87/1.77  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.87/1.77  tff(f_57, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.87/1.77  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.87/1.77  tff(f_71, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.87/1.77  tff(f_82, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.87/1.77  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.87/1.77  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.87/1.77  tff(f_65, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.87/1.77  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.87/1.77  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.87/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.87/1.77  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.87/1.77  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.87/1.77  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.87/1.77  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.87/1.77  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.87/1.77  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.87/1.77  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.87/1.77  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.87/1.77  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.87/1.77  tff(c_242, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.77  tff(c_246, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_242])).
% 3.87/1.77  tff(c_30, plain, (![A_27]: (k1_subset_1(A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.87/1.77  tff(c_32, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.77  tff(c_40, plain, (![A_34]: (k3_subset_1(A_34, k1_subset_1(A_34))=k2_subset_1(A_34))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.77  tff(c_57, plain, (![A_34]: (k3_subset_1(A_34, k1_subset_1(A_34))=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 3.87/1.77  tff(c_61, plain, (![A_34]: (k3_subset_1(A_34, k1_xboole_0)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 3.87/1.77  tff(c_46, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.87/1.77  tff(c_827, plain, (![A_91, B_92]: (k3_subset_1(A_91, k3_subset_1(A_91, B_92))=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.87/1.77  tff(c_829, plain, (![A_39]: (k3_subset_1(A_39, k3_subset_1(A_39, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_827])).
% 3.87/1.77  tff(c_833, plain, (![A_39]: (k3_subset_1(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_829])).
% 3.87/1.77  tff(c_359, plain, (![A_68, B_69]: (r1_tarski(A_68, B_69) | k4_xboole_0(A_68, B_69)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.77  tff(c_50, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.77  tff(c_60, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50])).
% 3.87/1.77  tff(c_138, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 3.87/1.77  tff(c_56, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.77  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56])).
% 3.87/1.77  tff(c_269, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_138, c_59])).
% 3.87/1.77  tff(c_270, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_269, c_138])).
% 3.87/1.77  tff(c_370, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_359, c_270])).
% 3.87/1.77  tff(c_835, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_833, c_370])).
% 3.87/1.77  tff(c_839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_835])).
% 3.87/1.77  tff(c_840, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_60])).
% 3.87/1.77  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.77  tff(c_36, plain, (![A_31]: (m1_subset_1(k2_subset_1(A_31), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.87/1.77  tff(c_58, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.87/1.77  tff(c_1671, plain, (![A_134, B_135]: (k3_subset_1(A_134, k3_subset_1(A_134, B_135))=B_135 | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.87/1.77  tff(c_1675, plain, (![A_39]: (k3_subset_1(A_39, k3_subset_1(A_39, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_1671])).
% 3.87/1.77  tff(c_1680, plain, (![A_39]: (k3_subset_1(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1675])).
% 3.87/1.77  tff(c_1894, plain, (![B_145, C_146, A_147]: (r1_tarski(B_145, C_146) | ~r1_tarski(k3_subset_1(A_147, C_146), k3_subset_1(A_147, B_145)) | ~m1_subset_1(C_146, k1_zfmisc_1(A_147)) | ~m1_subset_1(B_145, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.87/1.77  tff(c_1903, plain, (![B_145, A_39]: (r1_tarski(B_145, A_39) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_39, B_145)) | ~m1_subset_1(A_39, k1_zfmisc_1(A_39)) | ~m1_subset_1(B_145, k1_zfmisc_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_1894])).
% 3.87/1.77  tff(c_1925, plain, (![B_148, A_149]: (r1_tarski(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(A_149)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16, c_1903])).
% 3.87/1.77  tff(c_1935, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1925])).
% 3.87/1.77  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.77  tff(c_1945, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_1935, c_14])).
% 3.87/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.77  tff(c_123, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k3_xboole_0(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.77  tff(c_135, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k3_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_123])).
% 3.87/1.77  tff(c_1973, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1945, c_135])).
% 3.87/1.77  tff(c_22, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.87/1.77  tff(c_947, plain, (![A_101, B_102]: (k3_tarski(k2_tarski(A_101, B_102))=k2_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.87/1.77  tff(c_1081, plain, (![B_113, A_114]: (k3_tarski(k2_tarski(B_113, A_114))=k2_xboole_0(A_114, B_113))), inference(superposition, [status(thm), theory('equality')], [c_22, c_947])).
% 3.87/1.77  tff(c_28, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.87/1.77  tff(c_1087, plain, (![B_113, A_114]: (k2_xboole_0(B_113, A_114)=k2_xboole_0(A_114, B_113))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_28])).
% 3.87/1.77  tff(c_1764, plain, (![A_139, B_140]: (k4_xboole_0(A_139, B_140)=k3_subset_1(A_139, B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.77  tff(c_1774, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_1764])).
% 3.87/1.77  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.87/1.77  tff(c_1782, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1774, c_20])).
% 3.87/1.77  tff(c_1788, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1782])).
% 3.87/1.77  tff(c_2012, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1788])).
% 3.87/1.77  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.77  tff(c_982, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.77  tff(c_991, plain, (![A_108]: (k3_xboole_0(k1_xboole_0, A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_982])).
% 3.87/1.77  tff(c_996, plain, (![A_108]: (k2_xboole_0(A_108, k1_xboole_0)=A_108)), inference(superposition, [status(thm), theory('equality')], [c_991, c_135])).
% 3.87/1.77  tff(c_938, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k1_xboole_0 | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.77  tff(c_946, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_938])).
% 3.87/1.77  tff(c_1404, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k4_xboole_0(B_125, A_124))=k2_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.87/1.77  tff(c_1427, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_946, c_1404])).
% 3.87/1.77  tff(c_1434, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_996, c_1427])).
% 3.87/1.77  tff(c_1005, plain, (![A_108]: (k3_xboole_0(A_108, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_991, c_2])).
% 3.87/1.77  tff(c_1233, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.77  tff(c_1245, plain, (![A_108]: (k5_xboole_0(A_108, k1_xboole_0)=k4_xboole_0(A_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_1233])).
% 3.87/1.77  tff(c_1435, plain, (![A_108]: (k4_xboole_0(A_108, k1_xboole_0)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_1434, c_1245])).
% 3.87/1.77  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.77  tff(c_1946, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1935, c_8])).
% 3.87/1.77  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.77  tff(c_2004, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1946, c_18])).
% 3.87/1.77  tff(c_2010, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_2, c_2004])).
% 3.87/1.77  tff(c_841, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 3.87/1.77  tff(c_989, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_841, c_982])).
% 3.87/1.77  tff(c_1123, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_989])).
% 3.87/1.77  tff(c_1803, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k3_xboole_0(B_142, A_141))=k4_xboole_0(A_141, B_142))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1233])).
% 3.87/1.77  tff(c_1834, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_989, c_1803])).
% 3.87/1.77  tff(c_2722, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_1834])).
% 3.87/1.77  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.77  tff(c_1370, plain, (![A_122, B_123]: (k4_xboole_0(A_122, k4_xboole_0(A_122, B_123))=k3_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.77  tff(c_2181, plain, (![A_156, B_157]: (k4_xboole_0(A_156, k3_xboole_0(A_156, B_157))=k3_xboole_0(A_156, k4_xboole_0(A_156, B_157)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1370])).
% 3.87/1.77  tff(c_2190, plain, (![A_156, B_157]: (k5_xboole_0(k3_xboole_0(A_156, B_157), k3_xboole_0(A_156, k4_xboole_0(A_156, B_157)))=k2_xboole_0(k3_xboole_0(A_156, B_157), A_156))), inference(superposition, [status(thm), theory('equality')], [c_2181, c_20])).
% 3.87/1.77  tff(c_2236, plain, (![A_156, B_157]: (k5_xboole_0(k3_xboole_0(A_156, B_157), k3_xboole_0(A_156, k4_xboole_0(A_156, B_157)))=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1087, c_2190])).
% 3.87/1.77  tff(c_2729, plain, (k5_xboole_0(k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2')), k3_xboole_0('#skF_2', '#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2722, c_2236])).
% 3.87/1.77  tff(c_2749, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_4, c_2010, c_4, c_1123, c_4, c_2, c_2729])).
% 3.87/1.77  tff(c_2751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_840, c_2749])).
% 3.87/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.77  
% 3.87/1.77  Inference rules
% 3.87/1.77  ----------------------
% 3.87/1.77  #Ref     : 0
% 3.87/1.77  #Sup     : 648
% 3.87/1.77  #Fact    : 0
% 3.87/1.77  #Define  : 0
% 3.87/1.77  #Split   : 3
% 3.87/1.77  #Chain   : 0
% 3.87/1.77  #Close   : 0
% 3.87/1.77  
% 3.87/1.77  Ordering : KBO
% 3.87/1.77  
% 3.87/1.77  Simplification rules
% 3.87/1.77  ----------------------
% 3.87/1.77  #Subsume      : 22
% 3.87/1.77  #Demod        : 498
% 3.87/1.77  #Tautology    : 504
% 3.87/1.77  #SimpNegUnit  : 17
% 3.87/1.77  #BackRed      : 8
% 3.87/1.77  
% 3.87/1.77  #Partial instantiations: 0
% 3.87/1.77  #Strategies tried      : 1
% 3.87/1.77  
% 3.87/1.77  Timing (in seconds)
% 3.87/1.77  ----------------------
% 3.87/1.77  Preprocessing        : 0.35
% 3.87/1.77  Parsing              : 0.18
% 3.87/1.77  CNF conversion       : 0.02
% 3.87/1.77  Main loop            : 0.59
% 3.87/1.77  Inferencing          : 0.19
% 3.87/1.77  Reduction            : 0.24
% 3.87/1.77  Demodulation         : 0.19
% 3.87/1.77  BG Simplification    : 0.03
% 3.87/1.77  Subsumption          : 0.09
% 3.87/1.77  Abstraction          : 0.03
% 3.87/1.77  MUC search           : 0.00
% 3.87/1.77  Cooper               : 0.00
% 3.87/1.77  Total                : 0.98
% 3.87/1.77  Index Insertion      : 0.00
% 3.87/1.77  Index Deletion       : 0.00
% 3.87/1.77  Index Matching       : 0.00
% 3.87/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
