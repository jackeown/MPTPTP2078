%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 12.29s
% Output     : CNFRefutation 12.43s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 741 expanded)
%              Number of leaves         :   44 ( 270 expanded)
%              Depth                    :   19
%              Number of atoms          :  217 ( 949 expanded)
%              Number of equality atoms :  102 ( 563 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_62,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_121,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_1894,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,B_178)
      | k4_xboole_0(A_177,B_178) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_103,plain,(
    ~ r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1127,plain,(
    ! [A_134,B_135] :
      ( k4_xboole_0(A_134,B_135) = k3_subset_1(A_134,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1151,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1127])).

tff(c_30,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_672,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_698,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k4_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_672])).

tff(c_706,plain,(
    ! [A_110] : k4_xboole_0(A_110,k1_xboole_0) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_698])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_750,plain,(
    ! [A_111] : r1_tarski(A_111,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_26])).

tff(c_343,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k1_xboole_0
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_355,plain,(
    ! [A_21,B_22] : k4_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_343])).

tff(c_599,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_xboole_0(A_100,k4_xboole_0(C_101,B_102))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_611,plain,(
    ! [A_100,A_21] :
      ( r1_xboole_0(A_100,k1_xboole_0)
      | ~ r1_tarski(A_100,A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_599])).

tff(c_759,plain,(
    ! [A_111] : r1_xboole_0(A_111,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_750,c_611])).

tff(c_78,plain,
    ( r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7'))
    | r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_272,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_78])).

tff(c_354,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_272,c_343])).

tff(c_1401,plain,(
    ! [B_139,A_140,C_141] :
      ( r1_xboole_0(B_139,k4_xboole_0(A_140,C_141))
      | ~ r1_xboole_0(A_140,k4_xboole_0(B_139,C_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1430,plain,(
    ! [A_140] :
      ( r1_xboole_0('#skF_6',k4_xboole_0(A_140,'#skF_7'))
      | ~ r1_xboole_0(A_140,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_1401])).

tff(c_1560,plain,(
    ! [A_147] : r1_xboole_0('#skF_6',k4_xboole_0(A_147,'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_1430])).

tff(c_1566,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1560])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1566])).

tff(c_1586,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1906,plain,(
    k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1894,c_1586])).

tff(c_1947,plain,(
    ! [A_181,B_182] : k5_xboole_0(A_181,k3_xboole_0(A_181,B_182)) = k4_xboole_0(A_181,B_182) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1973,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k4_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1947])).

tff(c_1981,plain,(
    ! [A_183] : k4_xboole_0(A_183,k1_xboole_0) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1973])).

tff(c_1771,plain,(
    ! [A_159,B_160] :
      ( k2_xboole_0(A_159,B_160) = B_160
      | ~ r1_tarski(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1775,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),A_21) = A_21 ),
    inference(resolution,[status(thm)],[c_26,c_1771])).

tff(c_1998,plain,(
    ! [A_183] : k2_xboole_0(A_183,A_183) = A_183 ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_1775])).

tff(c_1683,plain,(
    ! [B_154,A_155] : k5_xboole_0(B_154,A_155) = k5_xboole_0(A_155,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1699,plain,(
    ! [A_155] : k5_xboole_0(k1_xboole_0,A_155) = A_155 ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_30])).

tff(c_1598,plain,(
    ! [B_151,A_152] : k3_xboole_0(B_151,A_152) = k3_xboole_0(A_152,B_151) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1614,plain,(
    ! [A_152] : k3_xboole_0(k1_xboole_0,A_152) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_24])).

tff(c_1979,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1973])).

tff(c_2127,plain,(
    ! [A_192,B_193] : k2_xboole_0(k3_xboole_0(A_192,B_193),k4_xboole_0(A_192,B_193)) = A_192 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2157,plain,(
    ! [A_20] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_20,k1_xboole_0)) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2127])).

tff(c_2164,plain,(
    ! [A_20] : k2_xboole_0(k1_xboole_0,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_2157])).

tff(c_2666,plain,(
    ! [A_228,B_229] : k5_xboole_0(k5_xboole_0(A_228,B_229),k2_xboole_0(A_228,B_229)) = k3_xboole_0(A_228,B_229) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2709,plain,(
    ! [A_20] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_20),A_20) = k3_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2164,c_2666])).

tff(c_2754,plain,(
    ! [A_230] : k5_xboole_0(A_230,A_230) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_1614,c_2709])).

tff(c_42,plain,(
    ! [A_40,B_41] : k5_xboole_0(k5_xboole_0(A_40,B_41),k2_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2759,plain,(
    ! [A_230] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_230,A_230)) = k3_xboole_0(A_230,A_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_42])).

tff(c_2790,plain,(
    ! [A_230] : k3_xboole_0(A_230,A_230) = A_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1998,c_1699,c_2759])).

tff(c_1816,plain,(
    ! [A_169,B_170] :
      ( k4_xboole_0(A_169,B_170) = k1_xboole_0
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1824,plain,(
    ! [A_21,B_22] : k4_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1816])).

tff(c_1991,plain,(
    ! [A_183] : k4_xboole_0(A_183,A_183) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_1824])).

tff(c_2136,plain,(
    ! [A_183] : k2_xboole_0(k3_xboole_0(A_183,A_183),k1_xboole_0) = A_183 ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_2127])).

tff(c_2798,plain,(
    ! [A_183] : k2_xboole_0(A_183,k1_xboole_0) = A_183 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2790,c_2136])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2202,plain,(
    ! [A_197,C_198,B_199] :
      ( r1_xboole_0(A_197,k4_xboole_0(C_198,B_199))
      | ~ r1_tarski(A_197,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2211,plain,(
    ! [A_197,A_20] :
      ( r1_xboole_0(A_197,A_20)
      | ~ r1_tarski(A_197,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1979,c_2202])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2031,plain,(
    ! [A_186,B_187,C_188] :
      ( ~ r1_xboole_0(A_186,B_187)
      | ~ r2_hidden(C_188,k3_xboole_0(A_186,B_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4227,plain,(
    ! [A_279,B_280] :
      ( ~ r1_xboole_0(A_279,B_280)
      | v1_xboole_0(k3_xboole_0(A_279,B_280)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2031])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1588,plain,(
    ! [B_148,A_149] :
      ( ~ v1_xboole_0(B_148)
      | B_148 = A_149
      | ~ v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1591,plain,(
    ! [A_149] :
      ( k1_xboole_0 = A_149
      | ~ v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_10,c_1588])).

tff(c_5030,plain,(
    ! [A_300,B_301] :
      ( k3_xboole_0(A_300,B_301) = k1_xboole_0
      | ~ r1_xboole_0(A_300,B_301) ) ),
    inference(resolution,[status(thm)],[c_4227,c_1591])).

tff(c_8278,plain,(
    ! [A_335,A_336] :
      ( k3_xboole_0(A_335,A_336) = k1_xboole_0
      | ~ r1_tarski(A_335,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2211,c_5030])).

tff(c_8291,plain,(
    ! [A_14,A_336] :
      ( k3_xboole_0(A_14,A_336) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_8278])).

tff(c_8311,plain,(
    ! [A_337,A_338] :
      ( k3_xboole_0(A_337,A_338) = k1_xboole_0
      | k1_xboole_0 != A_337 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_8291])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1967,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1947])).

tff(c_8341,plain,(
    ! [A_338,A_337] :
      ( k5_xboole_0(A_338,k1_xboole_0) = k4_xboole_0(A_338,A_337)
      | k1_xboole_0 != A_337 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8311,c_1967])).

tff(c_9410,plain,(
    ! [A_353,A_354] :
      ( k4_xboole_0(A_353,A_354) = A_353
      | k1_xboole_0 != A_354 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8341])).

tff(c_9680,plain,(
    ! [A_355,B_356] :
      ( k4_xboole_0(A_355,B_356) = k1_xboole_0
      | k1_xboole_0 != A_355 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1824,c_9410])).

tff(c_28,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9836,plain,(
    ! [A_355,B_356] :
      ( k2_xboole_0(k3_xboole_0(A_355,B_356),k1_xboole_0) = A_355
      | k1_xboole_0 != A_355 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9680,c_28])).

tff(c_10028,plain,(
    ! [B_356] : k3_xboole_0(k1_xboole_0,B_356) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_9836])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_66,plain,(
    ! [A_51] : ~ v1_xboole_0(k1_zfmisc_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2222,plain,(
    ! [B_201,A_202] :
      ( r2_hidden(B_201,A_202)
      | ~ m1_subset_1(B_201,A_202)
      | v1_xboole_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    ! [C_46,A_42] :
      ( r1_tarski(C_46,A_42)
      | ~ r2_hidden(C_46,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2233,plain,(
    ! [B_201,A_42] :
      ( r1_tarski(B_201,A_42)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_42))
      | v1_xboole_0(k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_2222,c_44])).

tff(c_2482,plain,(
    ! [B_220,A_221] :
      ( r1_tarski(B_220,A_221)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_221)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2233])).

tff(c_2507,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_2482])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2556,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2507,c_18])).

tff(c_2602,plain,(
    k2_xboole_0(k3_xboole_0('#skF_6','#skF_5'),k1_xboole_0) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_28])).

tff(c_3544,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_2798])).

tff(c_3210,plain,(
    ! [A_247,B_248] :
      ( k4_xboole_0(A_247,B_248) = k3_subset_1(A_247,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(A_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3235,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_3210])).

tff(c_5829,plain,(
    ! [A_311,B_312] : k5_xboole_0(A_311,k3_xboole_0(B_312,A_311)) = k4_xboole_0(A_311,B_312) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1947])).

tff(c_5892,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3544,c_5829])).

tff(c_5932,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3235,c_5892])).

tff(c_40,plain,(
    ! [A_37,B_38,C_39] : k5_xboole_0(k5_xboole_0(A_37,B_38),C_39) = k5_xboole_0(A_37,k5_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2762,plain,(
    ! [A_230,C_39] : k5_xboole_0(A_230,k5_xboole_0(A_230,C_39)) = k5_xboole_0(k1_xboole_0,C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_40])).

tff(c_2791,plain,(
    ! [A_230,C_39] : k5_xboole_0(A_230,k5_xboole_0(A_230,C_39)) = C_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_2762])).

tff(c_6810,plain,(
    k5_xboole_0('#skF_5',k3_subset_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5932,c_2791])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2557,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2507,c_22])).

tff(c_3299,plain,(
    k2_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3235,c_1775])).

tff(c_2669,plain,(
    ! [A_228,B_229] : k5_xboole_0(k3_xboole_0(A_228,B_229),k2_xboole_0(k5_xboole_0(A_228,B_229),k2_xboole_0(A_228,B_229))) = k3_xboole_0(k5_xboole_0(A_228,B_229),k2_xboole_0(A_228,B_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_42])).

tff(c_23769,plain,(
    ! [A_581,B_582] : k5_xboole_0(k3_xboole_0(A_581,B_582),k2_xboole_0(k5_xboole_0(A_581,B_582),k2_xboole_0(A_581,B_582))) = k3_xboole_0(k2_xboole_0(A_581,B_582),k5_xboole_0(A_581,B_582)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2669])).

tff(c_24015,plain,(
    k5_xboole_0(k3_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_5'),k2_xboole_0(k5_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_5'),'#skF_5')) = k3_xboole_0(k2_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_5'),k5_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3299,c_23769])).

tff(c_24136,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3544,c_2,c_6810,c_20,c_2557,c_4,c_6810,c_3299,c_4,c_4,c_2,c_24015])).

tff(c_1587,plain,(
    r1_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3234,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_3210])).

tff(c_34,plain,(
    ! [B_30,A_29,C_31] :
      ( r1_xboole_0(B_30,k4_xboole_0(A_29,C_31))
      | ~ r1_xboole_0(A_29,k4_xboole_0(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4107,plain,(
    ! [A_275] :
      ( r1_xboole_0('#skF_5',k4_xboole_0(A_275,'#skF_7'))
      | ~ r1_xboole_0(A_275,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3234,c_34])).

tff(c_4141,plain,(
    r1_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1587,c_4107])).

tff(c_5113,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4141,c_5030])).

tff(c_5513,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_7')) = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_20])).

tff(c_5530,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_7')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5513])).

tff(c_2001,plain,(
    ! [A_183] : r1_tarski(A_183,A_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_26])).

tff(c_2352,plain,(
    ! [A_211,A_212] :
      ( r1_xboole_0(A_211,k1_xboole_0)
      | ~ r1_tarski(A_211,A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1824,c_2202])).

tff(c_2364,plain,(
    ! [A_183] : r1_xboole_0(A_183,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2001,c_2352])).

tff(c_2508,plain,(
    ! [B_222,A_223,C_224] :
      ( r1_xboole_0(B_222,k4_xboole_0(A_223,C_224))
      | ~ r1_xboole_0(A_223,k4_xboole_0(B_222,C_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2523,plain,(
    ! [A_21,B_22,A_223] :
      ( r1_xboole_0(k4_xboole_0(A_21,B_22),k4_xboole_0(A_223,A_21))
      | ~ r1_xboole_0(A_223,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1824,c_2508])).

tff(c_10827,plain,(
    ! [A_374,B_375,A_376] : r1_xboole_0(k4_xboole_0(A_374,B_375),k4_xboole_0(A_376,A_374)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2523])).

tff(c_2521,plain,(
    ! [A_20,A_223] :
      ( r1_xboole_0(A_20,k4_xboole_0(A_223,k1_xboole_0))
      | ~ r1_xboole_0(A_223,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1979,c_2508])).

tff(c_2532,plain,(
    ! [A_20,A_223] :
      ( r1_xboole_0(A_20,A_223)
      | ~ r1_xboole_0(A_223,A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_2521])).

tff(c_11411,plain,(
    ! [A_386,A_387,B_388] : r1_xboole_0(k4_xboole_0(A_386,A_387),k4_xboole_0(A_387,B_388)) ),
    inference(resolution,[status(thm)],[c_10827,c_2532])).

tff(c_11878,plain,(
    ! [A_394,A_395,B_396] : r1_xboole_0(A_394,k4_xboole_0(k4_xboole_0(A_395,A_394),B_396)) ),
    inference(resolution,[status(thm)],[c_11411,c_34])).

tff(c_11923,plain,(
    ! [B_396] : r1_xboole_0(k4_xboole_0('#skF_6','#skF_7'),k4_xboole_0('#skF_5',B_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5530,c_11878])).

tff(c_24375,plain,(
    r1_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_24136,c_11923])).

tff(c_4258,plain,(
    ! [A_279,B_280] :
      ( k3_xboole_0(A_279,B_280) = k1_xboole_0
      | ~ r1_xboole_0(A_279,B_280) ) ),
    inference(resolution,[status(thm)],[c_4227,c_1591])).

tff(c_24615,plain,(
    k3_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24375,c_4258])).

tff(c_2712,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)),A_23) = k3_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2666])).

tff(c_24636,plain,(
    k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6')),k4_xboole_0('#skF_6','#skF_7')) = k3_xboole_0(k3_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6'),k4_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24615,c_2712])).

tff(c_24733,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10028,c_30,c_1824,c_2,c_1824,c_4,c_1699,c_2,c_24636])).

tff(c_24735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1906,c_24733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.29/5.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.29/5.20  
% 12.29/5.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.29/5.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 12.29/5.20  
% 12.29/5.20  %Foreground sorts:
% 12.29/5.20  
% 12.29/5.20  
% 12.29/5.20  %Background operators:
% 12.29/5.20  
% 12.29/5.20  
% 12.29/5.20  %Foreground operators:
% 12.29/5.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.29/5.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.29/5.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.29/5.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.29/5.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.29/5.20  tff('#skF_7', type, '#skF_7': $i).
% 12.29/5.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.29/5.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.29/5.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.29/5.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.29/5.20  tff('#skF_5', type, '#skF_5': $i).
% 12.29/5.20  tff('#skF_6', type, '#skF_6': $i).
% 12.29/5.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.29/5.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.29/5.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.29/5.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.29/5.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.29/5.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.29/5.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.29/5.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.29/5.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.29/5.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.29/5.20  
% 12.43/5.23  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.43/5.23  tff(f_131, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 12.43/5.23  tff(f_118, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.43/5.23  tff(f_68, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.43/5.23  tff(f_62, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.43/5.23  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.43/5.23  tff(f_64, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.43/5.23  tff(f_82, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 12.43/5.23  tff(f_78, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.43/5.23  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.43/5.23  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.43/5.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.43/5.23  tff(f_66, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.43/5.23  tff(f_94, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 12.43/5.23  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.43/5.23  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.43/5.23  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.43/5.23  tff(f_90, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 12.43/5.23  tff(f_121, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.43/5.23  tff(f_114, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.43/5.23  tff(f_101, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.43/5.23  tff(f_92, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.43/5.23  tff(c_1894, plain, (![A_177, B_178]: (r1_tarski(A_177, B_178) | k4_xboole_0(A_177, B_178)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.43/5.23  tff(c_72, plain, (~r1_tarski('#skF_6', '#skF_7') | ~r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.43/5.23  tff(c_103, plain, (~r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_72])).
% 12.43/5.23  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.43/5.23  tff(c_1127, plain, (![A_134, B_135]: (k4_xboole_0(A_134, B_135)=k3_subset_1(A_134, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.43/5.23  tff(c_1151, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1127])).
% 12.43/5.23  tff(c_30, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.43/5.23  tff(c_24, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.43/5.23  tff(c_672, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.43/5.23  tff(c_698, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k4_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_672])).
% 12.43/5.23  tff(c_706, plain, (![A_110]: (k4_xboole_0(A_110, k1_xboole_0)=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_698])).
% 12.43/5.23  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.43/5.23  tff(c_750, plain, (![A_111]: (r1_tarski(A_111, A_111))), inference(superposition, [status(thm), theory('equality')], [c_706, c_26])).
% 12.43/5.23  tff(c_343, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k1_xboole_0 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.43/5.23  tff(c_355, plain, (![A_21, B_22]: (k4_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_343])).
% 12.43/5.23  tff(c_599, plain, (![A_100, C_101, B_102]: (r1_xboole_0(A_100, k4_xboole_0(C_101, B_102)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.43/5.23  tff(c_611, plain, (![A_100, A_21]: (r1_xboole_0(A_100, k1_xboole_0) | ~r1_tarski(A_100, A_21))), inference(superposition, [status(thm), theory('equality')], [c_355, c_599])).
% 12.43/5.23  tff(c_759, plain, (![A_111]: (r1_xboole_0(A_111, k1_xboole_0))), inference(resolution, [status(thm)], [c_750, c_611])).
% 12.43/5.23  tff(c_78, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7')) | r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.43/5.23  tff(c_272, plain, (r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_103, c_78])).
% 12.43/5.23  tff(c_354, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_272, c_343])).
% 12.43/5.23  tff(c_1401, plain, (![B_139, A_140, C_141]: (r1_xboole_0(B_139, k4_xboole_0(A_140, C_141)) | ~r1_xboole_0(A_140, k4_xboole_0(B_139, C_141)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.43/5.23  tff(c_1430, plain, (![A_140]: (r1_xboole_0('#skF_6', k4_xboole_0(A_140, '#skF_7')) | ~r1_xboole_0(A_140, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_354, c_1401])).
% 12.43/5.23  tff(c_1560, plain, (![A_147]: (r1_xboole_0('#skF_6', k4_xboole_0(A_147, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_1430])).
% 12.43/5.23  tff(c_1566, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1560])).
% 12.43/5.23  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_1566])).
% 12.43/5.23  tff(c_1586, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 12.43/5.23  tff(c_1906, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1894, c_1586])).
% 12.43/5.23  tff(c_1947, plain, (![A_181, B_182]: (k5_xboole_0(A_181, k3_xboole_0(A_181, B_182))=k4_xboole_0(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.43/5.23  tff(c_1973, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k4_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1947])).
% 12.43/5.23  tff(c_1981, plain, (![A_183]: (k4_xboole_0(A_183, k1_xboole_0)=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1973])).
% 12.43/5.23  tff(c_1771, plain, (![A_159, B_160]: (k2_xboole_0(A_159, B_160)=B_160 | ~r1_tarski(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.43/5.23  tff(c_1775, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), A_21)=A_21)), inference(resolution, [status(thm)], [c_26, c_1771])).
% 12.43/5.23  tff(c_1998, plain, (![A_183]: (k2_xboole_0(A_183, A_183)=A_183)), inference(superposition, [status(thm), theory('equality')], [c_1981, c_1775])).
% 12.43/5.23  tff(c_1683, plain, (![B_154, A_155]: (k5_xboole_0(B_154, A_155)=k5_xboole_0(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.43/5.23  tff(c_1699, plain, (![A_155]: (k5_xboole_0(k1_xboole_0, A_155)=A_155)), inference(superposition, [status(thm), theory('equality')], [c_1683, c_30])).
% 12.43/5.23  tff(c_1598, plain, (![B_151, A_152]: (k3_xboole_0(B_151, A_152)=k3_xboole_0(A_152, B_151))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.43/5.23  tff(c_1614, plain, (![A_152]: (k3_xboole_0(k1_xboole_0, A_152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1598, c_24])).
% 12.43/5.23  tff(c_1979, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1973])).
% 12.43/5.23  tff(c_2127, plain, (![A_192, B_193]: (k2_xboole_0(k3_xboole_0(A_192, B_193), k4_xboole_0(A_192, B_193))=A_192)), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.43/5.23  tff(c_2157, plain, (![A_20]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_20, k1_xboole_0))=A_20)), inference(superposition, [status(thm), theory('equality')], [c_24, c_2127])).
% 12.43/5.23  tff(c_2164, plain, (![A_20]: (k2_xboole_0(k1_xboole_0, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_2157])).
% 12.43/5.23  tff(c_2666, plain, (![A_228, B_229]: (k5_xboole_0(k5_xboole_0(A_228, B_229), k2_xboole_0(A_228, B_229))=k3_xboole_0(A_228, B_229))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.43/5.23  tff(c_2709, plain, (![A_20]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_20), A_20)=k3_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_2164, c_2666])).
% 12.43/5.23  tff(c_2754, plain, (![A_230]: (k5_xboole_0(A_230, A_230)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_1614, c_2709])).
% 12.43/5.23  tff(c_42, plain, (![A_40, B_41]: (k5_xboole_0(k5_xboole_0(A_40, B_41), k2_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.43/5.23  tff(c_2759, plain, (![A_230]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_230, A_230))=k3_xboole_0(A_230, A_230))), inference(superposition, [status(thm), theory('equality')], [c_2754, c_42])).
% 12.43/5.23  tff(c_2790, plain, (![A_230]: (k3_xboole_0(A_230, A_230)=A_230)), inference(demodulation, [status(thm), theory('equality')], [c_1998, c_1699, c_2759])).
% 12.43/5.23  tff(c_1816, plain, (![A_169, B_170]: (k4_xboole_0(A_169, B_170)=k1_xboole_0 | ~r1_tarski(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.43/5.23  tff(c_1824, plain, (![A_21, B_22]: (k4_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1816])).
% 12.43/5.23  tff(c_1991, plain, (![A_183]: (k4_xboole_0(A_183, A_183)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1981, c_1824])).
% 12.43/5.23  tff(c_2136, plain, (![A_183]: (k2_xboole_0(k3_xboole_0(A_183, A_183), k1_xboole_0)=A_183)), inference(superposition, [status(thm), theory('equality')], [c_1991, c_2127])).
% 12.43/5.23  tff(c_2798, plain, (![A_183]: (k2_xboole_0(A_183, k1_xboole_0)=A_183)), inference(demodulation, [status(thm), theory('equality')], [c_2790, c_2136])).
% 12.43/5.23  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.43/5.23  tff(c_2202, plain, (![A_197, C_198, B_199]: (r1_xboole_0(A_197, k4_xboole_0(C_198, B_199)) | ~r1_tarski(A_197, B_199))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.43/5.23  tff(c_2211, plain, (![A_197, A_20]: (r1_xboole_0(A_197, A_20) | ~r1_tarski(A_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1979, c_2202])).
% 12.43/5.23  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.43/5.23  tff(c_2031, plain, (![A_186, B_187, C_188]: (~r1_xboole_0(A_186, B_187) | ~r2_hidden(C_188, k3_xboole_0(A_186, B_187)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.43/5.23  tff(c_4227, plain, (![A_279, B_280]: (~r1_xboole_0(A_279, B_280) | v1_xboole_0(k3_xboole_0(A_279, B_280)))), inference(resolution, [status(thm)], [c_8, c_2031])).
% 12.43/5.23  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.43/5.23  tff(c_1588, plain, (![B_148, A_149]: (~v1_xboole_0(B_148) | B_148=A_149 | ~v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.43/5.23  tff(c_1591, plain, (![A_149]: (k1_xboole_0=A_149 | ~v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_10, c_1588])).
% 12.43/5.23  tff(c_5030, plain, (![A_300, B_301]: (k3_xboole_0(A_300, B_301)=k1_xboole_0 | ~r1_xboole_0(A_300, B_301))), inference(resolution, [status(thm)], [c_4227, c_1591])).
% 12.43/5.23  tff(c_8278, plain, (![A_335, A_336]: (k3_xboole_0(A_335, A_336)=k1_xboole_0 | ~r1_tarski(A_335, k1_xboole_0))), inference(resolution, [status(thm)], [c_2211, c_5030])).
% 12.43/5.23  tff(c_8291, plain, (![A_14, A_336]: (k3_xboole_0(A_14, A_336)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_8278])).
% 12.43/5.23  tff(c_8311, plain, (![A_337, A_338]: (k3_xboole_0(A_337, A_338)=k1_xboole_0 | k1_xboole_0!=A_337)), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_8291])).
% 12.43/5.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.43/5.23  tff(c_1967, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1947])).
% 12.43/5.23  tff(c_8341, plain, (![A_338, A_337]: (k5_xboole_0(A_338, k1_xboole_0)=k4_xboole_0(A_338, A_337) | k1_xboole_0!=A_337)), inference(superposition, [status(thm), theory('equality')], [c_8311, c_1967])).
% 12.43/5.23  tff(c_9410, plain, (![A_353, A_354]: (k4_xboole_0(A_353, A_354)=A_353 | k1_xboole_0!=A_354)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8341])).
% 12.43/5.23  tff(c_9680, plain, (![A_355, B_356]: (k4_xboole_0(A_355, B_356)=k1_xboole_0 | k1_xboole_0!=A_355)), inference(superposition, [status(thm), theory('equality')], [c_1824, c_9410])).
% 12.43/5.23  tff(c_28, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.43/5.23  tff(c_9836, plain, (![A_355, B_356]: (k2_xboole_0(k3_xboole_0(A_355, B_356), k1_xboole_0)=A_355 | k1_xboole_0!=A_355)), inference(superposition, [status(thm), theory('equality')], [c_9680, c_28])).
% 12.43/5.23  tff(c_10028, plain, (![B_356]: (k3_xboole_0(k1_xboole_0, B_356)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_9836])).
% 12.43/5.23  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.43/5.23  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.43/5.23  tff(c_66, plain, (![A_51]: (~v1_xboole_0(k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.43/5.23  tff(c_2222, plain, (![B_201, A_202]: (r2_hidden(B_201, A_202) | ~m1_subset_1(B_201, A_202) | v1_xboole_0(A_202))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.43/5.23  tff(c_44, plain, (![C_46, A_42]: (r1_tarski(C_46, A_42) | ~r2_hidden(C_46, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.43/5.23  tff(c_2233, plain, (![B_201, A_42]: (r1_tarski(B_201, A_42) | ~m1_subset_1(B_201, k1_zfmisc_1(A_42)) | v1_xboole_0(k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_2222, c_44])).
% 12.43/5.23  tff(c_2482, plain, (![B_220, A_221]: (r1_tarski(B_220, A_221) | ~m1_subset_1(B_220, k1_zfmisc_1(A_221)))), inference(negUnitSimplification, [status(thm)], [c_66, c_2233])).
% 12.43/5.23  tff(c_2507, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_2482])).
% 12.43/5.23  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.43/5.23  tff(c_2556, plain, (k4_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2507, c_18])).
% 12.43/5.23  tff(c_2602, plain, (k2_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), k1_xboole_0)='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2556, c_28])).
% 12.43/5.23  tff(c_3544, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2602, c_2798])).
% 12.43/5.23  tff(c_3210, plain, (![A_247, B_248]: (k4_xboole_0(A_247, B_248)=k3_subset_1(A_247, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(A_247)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.43/5.23  tff(c_3235, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_3210])).
% 12.43/5.23  tff(c_5829, plain, (![A_311, B_312]: (k5_xboole_0(A_311, k3_xboole_0(B_312, A_311))=k4_xboole_0(A_311, B_312))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1947])).
% 12.43/5.23  tff(c_5892, plain, (k5_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3544, c_5829])).
% 12.43/5.23  tff(c_5932, plain, (k5_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3235, c_5892])).
% 12.43/5.23  tff(c_40, plain, (![A_37, B_38, C_39]: (k5_xboole_0(k5_xboole_0(A_37, B_38), C_39)=k5_xboole_0(A_37, k5_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.43/5.23  tff(c_2762, plain, (![A_230, C_39]: (k5_xboole_0(A_230, k5_xboole_0(A_230, C_39))=k5_xboole_0(k1_xboole_0, C_39))), inference(superposition, [status(thm), theory('equality')], [c_2754, c_40])).
% 12.43/5.23  tff(c_2791, plain, (![A_230, C_39]: (k5_xboole_0(A_230, k5_xboole_0(A_230, C_39))=C_39)), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_2762])).
% 12.43/5.23  tff(c_6810, plain, (k5_xboole_0('#skF_5', k3_subset_1('#skF_5', '#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_5932, c_2791])).
% 12.43/5.23  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.43/5.23  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.43/5.23  tff(c_2557, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_2507, c_22])).
% 12.43/5.23  tff(c_3299, plain, (k2_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3235, c_1775])).
% 12.43/5.23  tff(c_2669, plain, (![A_228, B_229]: (k5_xboole_0(k3_xboole_0(A_228, B_229), k2_xboole_0(k5_xboole_0(A_228, B_229), k2_xboole_0(A_228, B_229)))=k3_xboole_0(k5_xboole_0(A_228, B_229), k2_xboole_0(A_228, B_229)))), inference(superposition, [status(thm), theory('equality')], [c_2666, c_42])).
% 12.43/5.23  tff(c_23769, plain, (![A_581, B_582]: (k5_xboole_0(k3_xboole_0(A_581, B_582), k2_xboole_0(k5_xboole_0(A_581, B_582), k2_xboole_0(A_581, B_582)))=k3_xboole_0(k2_xboole_0(A_581, B_582), k5_xboole_0(A_581, B_582)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2669])).
% 12.43/5.23  tff(c_24015, plain, (k5_xboole_0(k3_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_5'), k2_xboole_0(k5_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_5'), '#skF_5'))=k3_xboole_0(k2_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_5'), k5_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3299, c_23769])).
% 12.43/5.23  tff(c_24136, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3544, c_2, c_6810, c_20, c_2557, c_4, c_6810, c_3299, c_4, c_4, c_2, c_24015])).
% 12.43/5.23  tff(c_1587, plain, (r1_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_72])).
% 12.43/5.23  tff(c_3234, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_3210])).
% 12.43/5.23  tff(c_34, plain, (![B_30, A_29, C_31]: (r1_xboole_0(B_30, k4_xboole_0(A_29, C_31)) | ~r1_xboole_0(A_29, k4_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.43/5.23  tff(c_4107, plain, (![A_275]: (r1_xboole_0('#skF_5', k4_xboole_0(A_275, '#skF_7')) | ~r1_xboole_0(A_275, k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3234, c_34])).
% 12.43/5.23  tff(c_4141, plain, (r1_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1587, c_4107])).
% 12.43/5.23  tff(c_5113, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4141, c_5030])).
% 12.43/5.23  tff(c_5513, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5113, c_20])).
% 12.43/5.23  tff(c_5530, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5513])).
% 12.43/5.23  tff(c_2001, plain, (![A_183]: (r1_tarski(A_183, A_183))), inference(superposition, [status(thm), theory('equality')], [c_1981, c_26])).
% 12.43/5.23  tff(c_2352, plain, (![A_211, A_212]: (r1_xboole_0(A_211, k1_xboole_0) | ~r1_tarski(A_211, A_212))), inference(superposition, [status(thm), theory('equality')], [c_1824, c_2202])).
% 12.43/5.23  tff(c_2364, plain, (![A_183]: (r1_xboole_0(A_183, k1_xboole_0))), inference(resolution, [status(thm)], [c_2001, c_2352])).
% 12.43/5.23  tff(c_2508, plain, (![B_222, A_223, C_224]: (r1_xboole_0(B_222, k4_xboole_0(A_223, C_224)) | ~r1_xboole_0(A_223, k4_xboole_0(B_222, C_224)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.43/5.23  tff(c_2523, plain, (![A_21, B_22, A_223]: (r1_xboole_0(k4_xboole_0(A_21, B_22), k4_xboole_0(A_223, A_21)) | ~r1_xboole_0(A_223, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1824, c_2508])).
% 12.43/5.23  tff(c_10827, plain, (![A_374, B_375, A_376]: (r1_xboole_0(k4_xboole_0(A_374, B_375), k4_xboole_0(A_376, A_374)))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2523])).
% 12.43/5.23  tff(c_2521, plain, (![A_20, A_223]: (r1_xboole_0(A_20, k4_xboole_0(A_223, k1_xboole_0)) | ~r1_xboole_0(A_223, A_20))), inference(superposition, [status(thm), theory('equality')], [c_1979, c_2508])).
% 12.43/5.23  tff(c_2532, plain, (![A_20, A_223]: (r1_xboole_0(A_20, A_223) | ~r1_xboole_0(A_223, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_2521])).
% 12.43/5.23  tff(c_11411, plain, (![A_386, A_387, B_388]: (r1_xboole_0(k4_xboole_0(A_386, A_387), k4_xboole_0(A_387, B_388)))), inference(resolution, [status(thm)], [c_10827, c_2532])).
% 12.43/5.23  tff(c_11878, plain, (![A_394, A_395, B_396]: (r1_xboole_0(A_394, k4_xboole_0(k4_xboole_0(A_395, A_394), B_396)))), inference(resolution, [status(thm)], [c_11411, c_34])).
% 12.43/5.23  tff(c_11923, plain, (![B_396]: (r1_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), k4_xboole_0('#skF_5', B_396)))), inference(superposition, [status(thm), theory('equality')], [c_5530, c_11878])).
% 12.43/5.23  tff(c_24375, plain, (r1_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_24136, c_11923])).
% 12.43/5.23  tff(c_4258, plain, (![A_279, B_280]: (k3_xboole_0(A_279, B_280)=k1_xboole_0 | ~r1_xboole_0(A_279, B_280))), inference(resolution, [status(thm)], [c_4227, c_1591])).
% 12.43/5.23  tff(c_24615, plain, (k3_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_24375, c_4258])).
% 12.43/5.23  tff(c_2712, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24)), A_23)=k3_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2666])).
% 12.43/5.23  tff(c_24636, plain, (k5_xboole_0(k5_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6')), k4_xboole_0('#skF_6', '#skF_7'))=k3_xboole_0(k3_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6'), k4_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_24615, c_2712])).
% 12.43/5.23  tff(c_24733, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10028, c_30, c_1824, c_2, c_1824, c_4, c_1699, c_2, c_24636])).
% 12.43/5.23  tff(c_24735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1906, c_24733])).
% 12.43/5.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.43/5.23  
% 12.43/5.23  Inference rules
% 12.43/5.23  ----------------------
% 12.43/5.23  #Ref     : 1
% 12.43/5.23  #Sup     : 6399
% 12.43/5.23  #Fact    : 0
% 12.43/5.23  #Define  : 0
% 12.43/5.23  #Split   : 11
% 12.43/5.23  #Chain   : 0
% 12.43/5.23  #Close   : 0
% 12.43/5.23  
% 12.43/5.23  Ordering : KBO
% 12.43/5.23  
% 12.43/5.23  Simplification rules
% 12.43/5.23  ----------------------
% 12.43/5.23  #Subsume      : 1173
% 12.43/5.23  #Demod        : 5306
% 12.43/5.23  #Tautology    : 3158
% 12.43/5.23  #SimpNegUnit  : 226
% 12.43/5.23  #BackRed      : 18
% 12.43/5.23  
% 12.43/5.23  #Partial instantiations: 0
% 12.43/5.23  #Strategies tried      : 1
% 12.43/5.23  
% 12.43/5.23  Timing (in seconds)
% 12.43/5.23  ----------------------
% 12.56/5.23  Preprocessing        : 0.34
% 12.56/5.23  Parsing              : 0.18
% 12.56/5.23  CNF conversion       : 0.03
% 12.56/5.23  Main loop            : 4.12
% 12.56/5.23  Inferencing          : 0.80
% 12.56/5.23  Reduction            : 2.21
% 12.56/5.23  Demodulation         : 1.83
% 12.56/5.23  BG Simplification    : 0.08
% 12.56/5.23  Subsumption          : 0.80
% 12.56/5.23  Abstraction          : 0.12
% 12.56/5.23  MUC search           : 0.00
% 12.56/5.23  Cooper               : 0.00
% 12.56/5.23  Total                : 4.52
% 12.56/5.23  Index Insertion      : 0.00
% 12.56/5.23  Index Deletion       : 0.00
% 12.56/5.23  Index Matching       : 0.00
% 12.56/5.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
