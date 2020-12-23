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
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 196 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 300 expanded)
%              Number of equality atoms :   61 ( 120 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_82,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_268,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_275,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_268])).

tff(c_382,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_401,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_382])).

tff(c_417,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_401])).

tff(c_46,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_68])).

tff(c_120,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_121,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60])).

tff(c_829,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_839,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_829])).

tff(c_846,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_839])).

tff(c_62,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_71,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_266,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_71])).

tff(c_849,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_266])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_849])).

tff(c_853,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_50,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [C_21,A_17] :
      ( r2_hidden(C_21,k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1299,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(B_120,A_121)
      | ~ r2_hidden(B_120,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1305,plain,(
    ! [C_21,A_17] :
      ( m1_subset_1(C_21,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_1299])).

tff(c_1309,plain,(
    ! [C_21,A_17] :
      ( m1_subset_1(C_21,k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1305])).

tff(c_854,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1131,plain,(
    ! [B_108,A_109] :
      ( r2_hidden(B_108,A_109)
      | ~ m1_subset_1(B_108,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1135,plain,(
    ! [B_108,A_17] :
      ( r1_tarski(B_108,A_17)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1131,c_24])).

tff(c_1139,plain,(
    ! [B_110,A_111] :
      ( r1_tarski(B_110,A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1135])).

tff(c_1153,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1139])).

tff(c_1268,plain,(
    ! [B_117,A_118] :
      ( B_117 = A_118
      | ~ r1_tarski(B_117,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1270,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1153,c_1268])).

tff(c_1279,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_1270])).

tff(c_1395,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,B_127) = k3_subset_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1413,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1395])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1198,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1153,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1154,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k3_xboole_0(A_112,B_113)) = k4_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1320,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k3_xboole_0(B_125,A_124)) = k4_xboole_0(A_124,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1154])).

tff(c_1337,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_1320])).

tff(c_1415,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1413,c_1337])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_897,plain,(
    ! [B_92,A_93] : k5_xboole_0(B_92,A_93) = k5_xboole_0(A_93,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_913,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,A_93) = A_93 ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_18])).

tff(c_1447,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k5_xboole_0(A_128,B_129),C_130) = k5_xboole_0(A_128,k5_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1521,plain,(
    ! [A_16,C_130] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_130)) = k5_xboole_0(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1447])).

tff(c_1542,plain,(
    ! [A_131,C_132] : k5_xboole_0(A_131,k5_xboole_0(A_131,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_1521])).

tff(c_1616,plain,(
    ! [A_133,B_134] : k5_xboole_0(A_133,k5_xboole_0(B_134,A_133)) = B_134 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1542])).

tff(c_1666,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_1616])).

tff(c_996,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1006,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_853,c_996])).

tff(c_1344,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_1320])).

tff(c_2263,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1666,c_1344])).

tff(c_3734,plain,(
    ! [A_183,C_184] :
      ( k4_xboole_0(A_183,C_184) = k3_subset_1(A_183,C_184)
      | ~ r1_tarski(C_184,A_183) ) ),
    inference(resolution,[status(thm)],[c_1309,c_1395])).

tff(c_3749,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_853,c_3734])).

tff(c_3762,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_3749])).

tff(c_58,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ! [A_24] : k1_subset_1(A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [A_29] : k3_subset_1(A_29,k1_subset_1(A_29)) = k2_subset_1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    ! [A_29] : k3_subset_1(A_29,k1_subset_1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_72,plain,(
    ! [A_29] : k3_subset_1(A_29,k1_xboole_0) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_69])).

tff(c_2747,plain,(
    ! [A_161,C_162,B_163] :
      ( r1_tarski(k3_subset_1(A_161,C_162),k3_subset_1(A_161,B_163))
      | ~ r1_tarski(B_163,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_161))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2758,plain,(
    ! [A_29,C_162] :
      ( r1_tarski(k3_subset_1(A_29,C_162),A_29)
      | ~ r1_tarski(k1_xboole_0,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2747])).

tff(c_2764,plain,(
    ! [A_29,C_162] :
      ( r1_tarski(k3_subset_1(A_29,C_162),A_29)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16,c_2758])).

tff(c_3806,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3762,c_2764])).

tff(c_3821,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_3806])).

tff(c_4385,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1309,c_3821])).

tff(c_4392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_4385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.01  
% 5.01/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.01  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.01/2.01  
% 5.01/2.01  %Foreground sorts:
% 5.01/2.01  
% 5.01/2.01  
% 5.01/2.01  %Background operators:
% 5.01/2.01  
% 5.01/2.01  
% 5.01/2.01  %Foreground operators:
% 5.01/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.01/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/2.01  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.01/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.01/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.01/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/2.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.01/2.01  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.01/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.01/2.01  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.01/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.01/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/2.01  
% 5.01/2.03  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.01/2.03  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.01/2.03  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.01/2.03  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.01/2.03  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.01/2.03  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.01/2.03  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 5.01/2.03  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.01/2.03  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.01/2.03  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.01/2.03  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.01/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.01/2.03  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.01/2.03  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.01/2.03  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.01/2.03  tff(f_93, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.01/2.03  tff(f_71, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.01/2.03  tff(f_82, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 5.01/2.03  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.01/2.03  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.01/2.03  tff(c_22, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.01/2.03  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/2.03  tff(c_268, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/2.03  tff(c_275, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_268])).
% 5.01/2.03  tff(c_382, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/2.03  tff(c_401, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_275, c_382])).
% 5.01/2.03  tff(c_417, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_401])).
% 5.01/2.03  tff(c_46, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.01/2.03  tff(c_68, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.01/2.03  tff(c_70, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_68])).
% 5.01/2.03  tff(c_120, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_70])).
% 5.01/2.03  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.01/2.03  tff(c_121, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60])).
% 5.01/2.03  tff(c_829, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.01/2.03  tff(c_839, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_121, c_829])).
% 5.01/2.04  tff(c_846, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_417, c_839])).
% 5.01/2.04  tff(c_62, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.01/2.04  tff(c_71, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 5.01/2.04  tff(c_266, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_71])).
% 5.01/2.04  tff(c_849, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_266])).
% 5.01/2.04  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_849])).
% 5.01/2.04  tff(c_853, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 5.01/2.04  tff(c_50, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.01/2.04  tff(c_26, plain, (![C_21, A_17]: (r2_hidden(C_21, k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.04  tff(c_1299, plain, (![B_120, A_121]: (m1_subset_1(B_120, A_121) | ~r2_hidden(B_120, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.01/2.04  tff(c_1305, plain, (![C_21, A_17]: (m1_subset_1(C_21, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(resolution, [status(thm)], [c_26, c_1299])).
% 5.01/2.04  tff(c_1309, plain, (![C_21, A_17]: (m1_subset_1(C_21, k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(negUnitSimplification, [status(thm)], [c_50, c_1305])).
% 5.01/2.04  tff(c_854, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 5.01/2.04  tff(c_1131, plain, (![B_108, A_109]: (r2_hidden(B_108, A_109) | ~m1_subset_1(B_108, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.01/2.04  tff(c_24, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/2.04  tff(c_1135, plain, (![B_108, A_17]: (r1_tarski(B_108, A_17) | ~m1_subset_1(B_108, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_1131, c_24])).
% 5.01/2.04  tff(c_1139, plain, (![B_110, A_111]: (r1_tarski(B_110, A_111) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)))), inference(negUnitSimplification, [status(thm)], [c_50, c_1135])).
% 5.01/2.04  tff(c_1153, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1139])).
% 5.01/2.04  tff(c_1268, plain, (![B_117, A_118]: (B_117=A_118 | ~r1_tarski(B_117, A_118) | ~r1_tarski(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/2.04  tff(c_1270, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1153, c_1268])).
% 5.01/2.04  tff(c_1279, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_854, c_1270])).
% 5.01/2.04  tff(c_1395, plain, (![A_126, B_127]: (k4_xboole_0(A_126, B_127)=k3_subset_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.01/2.04  tff(c_1413, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_1395])).
% 5.01/2.04  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/2.04  tff(c_1198, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1153, c_14])).
% 5.01/2.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/2.04  tff(c_1154, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k3_xboole_0(A_112, B_113))=k4_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/2.04  tff(c_1320, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k3_xboole_0(B_125, A_124))=k4_xboole_0(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1154])).
% 5.01/2.04  tff(c_1337, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1198, c_1320])).
% 5.01/2.04  tff(c_1415, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1413, c_1337])).
% 5.01/2.04  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.01/2.04  tff(c_897, plain, (![B_92, A_93]: (k5_xboole_0(B_92, A_93)=k5_xboole_0(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.01/2.04  tff(c_18, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/2.04  tff(c_913, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, A_93)=A_93)), inference(superposition, [status(thm), theory('equality')], [c_897, c_18])).
% 5.01/2.04  tff(c_1447, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k5_xboole_0(A_128, B_129), C_130)=k5_xboole_0(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.01/2.04  tff(c_1521, plain, (![A_16, C_130]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_130))=k5_xboole_0(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1447])).
% 5.01/2.04  tff(c_1542, plain, (![A_131, C_132]: (k5_xboole_0(A_131, k5_xboole_0(A_131, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_913, c_1521])).
% 5.01/2.04  tff(c_1616, plain, (![A_133, B_134]: (k5_xboole_0(A_133, k5_xboole_0(B_134, A_133))=B_134)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1542])).
% 5.01/2.04  tff(c_1666, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1415, c_1616])).
% 5.01/2.04  tff(c_996, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/2.04  tff(c_1006, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_853, c_996])).
% 5.01/2.04  tff(c_1344, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1006, c_1320])).
% 5.01/2.04  tff(c_2263, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1666, c_1344])).
% 5.01/2.04  tff(c_3734, plain, (![A_183, C_184]: (k4_xboole_0(A_183, C_184)=k3_subset_1(A_183, C_184) | ~r1_tarski(C_184, A_183))), inference(resolution, [status(thm)], [c_1309, c_1395])).
% 5.01/2.04  tff(c_3749, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_853, c_3734])).
% 5.01/2.04  tff(c_3762, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2263, c_3749])).
% 5.01/2.04  tff(c_58, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.01/2.04  tff(c_44, plain, (![A_24]: (k1_subset_1(A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.01/2.04  tff(c_52, plain, (![A_29]: (k3_subset_1(A_29, k1_subset_1(A_29))=k2_subset_1(A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.01/2.04  tff(c_69, plain, (![A_29]: (k3_subset_1(A_29, k1_subset_1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 5.01/2.04  tff(c_72, plain, (![A_29]: (k3_subset_1(A_29, k1_xboole_0)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_69])).
% 5.01/2.04  tff(c_2747, plain, (![A_161, C_162, B_163]: (r1_tarski(k3_subset_1(A_161, C_162), k3_subset_1(A_161, B_163)) | ~r1_tarski(B_163, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(A_161)) | ~m1_subset_1(B_163, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.01/2.04  tff(c_2758, plain, (![A_29, C_162]: (r1_tarski(k3_subset_1(A_29, C_162), A_29) | ~r1_tarski(k1_xboole_0, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(A_29)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2747])).
% 5.01/2.04  tff(c_2764, plain, (![A_29, C_162]: (r1_tarski(k3_subset_1(A_29, C_162), A_29) | ~m1_subset_1(C_162, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16, c_2758])).
% 5.01/2.04  tff(c_3806, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3762, c_2764])).
% 5.01/2.04  tff(c_3821, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1279, c_3806])).
% 5.01/2.04  tff(c_4385, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1309, c_3821])).
% 5.01/2.04  tff(c_4392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_853, c_4385])).
% 5.01/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.04  
% 5.01/2.04  Inference rules
% 5.01/2.04  ----------------------
% 5.01/2.04  #Ref     : 0
% 5.01/2.04  #Sup     : 1065
% 5.01/2.04  #Fact    : 0
% 5.01/2.04  #Define  : 0
% 5.01/2.04  #Split   : 2
% 5.01/2.04  #Chain   : 0
% 5.01/2.04  #Close   : 0
% 5.01/2.04  
% 5.01/2.04  Ordering : KBO
% 5.01/2.04  
% 5.01/2.04  Simplification rules
% 5.01/2.04  ----------------------
% 5.01/2.04  #Subsume      : 35
% 5.01/2.04  #Demod        : 778
% 5.01/2.04  #Tautology    : 666
% 5.01/2.04  #SimpNegUnit  : 6
% 5.01/2.04  #BackRed      : 6
% 5.01/2.04  
% 5.01/2.04  #Partial instantiations: 0
% 5.01/2.04  #Strategies tried      : 1
% 5.01/2.04  
% 5.01/2.04  Timing (in seconds)
% 5.01/2.04  ----------------------
% 5.01/2.04  Preprocessing        : 0.34
% 5.01/2.04  Parsing              : 0.18
% 5.01/2.04  CNF conversion       : 0.02
% 5.01/2.04  Main loop            : 0.92
% 5.01/2.04  Inferencing          : 0.29
% 5.01/2.04  Reduction            : 0.40
% 5.01/2.04  Demodulation         : 0.33
% 5.01/2.04  BG Simplification    : 0.04
% 5.01/2.04  Subsumption          : 0.13
% 5.01/2.04  Abstraction          : 0.04
% 5.01/2.04  MUC search           : 0.00
% 5.01/2.04  Cooper               : 0.00
% 5.01/2.04  Total                : 1.31
% 5.01/2.04  Index Insertion      : 0.00
% 5.01/2.04  Index Deletion       : 0.00
% 5.01/2.04  Index Matching       : 0.00
% 5.01/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
