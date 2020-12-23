%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 275 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 364 expanded)
%              Number of equality atoms :   63 ( 213 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_22,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_254,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_262,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_254])).

tff(c_289,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_302,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_289])).

tff(c_316,plain,(
    ! [B_58] : k4_xboole_0(B_58,B_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_302])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_321,plain,(
    ! [B_58] : r1_tarski(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_16])).

tff(c_315,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_302])).

tff(c_44,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_180,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_181,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_50])).

tff(c_450,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_457,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_450])).

tff(c_460,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_457])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_244,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_180,c_60])).

tff(c_461,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_244])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_461])).

tff(c_466,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_48,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_624,plain,(
    ! [B_86,A_87] :
      ( r2_hidden(B_86,A_87)
      | ~ m1_subset_1(B_86,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_631,plain,(
    ! [B_86,A_18] :
      ( r1_tarski(B_86,A_18)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_624,c_24])).

tff(c_831,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_631])).

tff(c_844,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_831])).

tff(c_1305,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1318,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1305])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_853,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_844,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_583,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1365,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(B_112,A_111)) = k4_xboole_0(A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_583])).

tff(c_1404,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_1365])).

tff(c_1442,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_1404])).

tff(c_133,plain,(
    ! [B_38,A_39] : k5_xboole_0(B_38,A_39) = k5_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_149,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_18])).

tff(c_854,plain,(
    ! [A_98,B_99,C_100] : k5_xboole_0(k5_xboole_0(A_98,B_99),C_100) = k5_xboole_0(A_98,k5_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_918,plain,(
    ! [A_17,C_100] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_100)) = k5_xboole_0(k1_xboole_0,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_854])).

tff(c_931,plain,(
    ! [A_17,C_100] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_918])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_948,plain,(
    ! [A_101,C_102] : k5_xboole_0(A_101,k5_xboole_0(A_101,C_102)) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_918])).

tff(c_1014,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k5_xboole_0(B_104,A_103)) = B_104 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_948])).

tff(c_1047,plain,(
    ! [A_17,C_100] : k5_xboole_0(k5_xboole_0(A_17,C_100),C_100) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1014])).

tff(c_1474,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1047])).

tff(c_465,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_528,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_538,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_465,c_528])).

tff(c_563,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_538])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2452,plain,(
    ! [B_139,A_140,B_141] : k5_xboole_0(B_139,k5_xboole_0(A_140,B_141)) = k5_xboole_0(A_140,k5_xboole_0(B_141,B_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_854])).

tff(c_2850,plain,(
    ! [A_142,B_143] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_142,B_143)) = k5_xboole_0(B_143,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2452])).

tff(c_2976,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2850])).

tff(c_3498,plain,(
    ! [A_148,B_149] : k5_xboole_0(k3_xboole_0(A_148,B_149),A_148) = k4_xboole_0(A_148,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2976])).

tff(c_3581,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_3498])).

tff(c_3627,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_3581])).

tff(c_785,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_796,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_16,c_785])).

tff(c_3655,plain,
    ( k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3627,c_796])).

tff(c_3677,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_3627,c_3655])).

tff(c_3679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_3677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.81  
% 4.35/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.35/1.82  
% 4.35/1.82  %Foreground sorts:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Background operators:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Foreground operators:
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.35/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.35/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.35/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.82  
% 4.35/1.83  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.35/1.83  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.35/1.83  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.35/1.83  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.35/1.83  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.35/1.83  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.35/1.83  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 4.35/1.83  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.35/1.83  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.35/1.83  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.35/1.83  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.35/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.35/1.83  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.35/1.83  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.35/1.83  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.35/1.83  tff(c_22, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.35/1.83  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.35/1.83  tff(c_254, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/1.83  tff(c_262, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_254])).
% 4.35/1.83  tff(c_289, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/1.83  tff(c_302, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_262, c_289])).
% 4.35/1.83  tff(c_316, plain, (![B_58]: (k4_xboole_0(B_58, B_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_302])).
% 4.35/1.83  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.35/1.83  tff(c_321, plain, (![B_58]: (r1_tarski(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_316, c_16])).
% 4.35/1.83  tff(c_315, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_302])).
% 4.35/1.83  tff(c_44, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.35/1.83  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.83  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 4.35/1.83  tff(c_180, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_59])).
% 4.35/1.83  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.83  tff(c_181, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_50])).
% 4.35/1.83  tff(c_450, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.83  tff(c_457, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_181, c_450])).
% 4.35/1.83  tff(c_460, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_315, c_457])).
% 4.35/1.83  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.83  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 4.35/1.83  tff(c_244, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_180, c_60])).
% 4.35/1.83  tff(c_461, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_244])).
% 4.35/1.83  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_321, c_461])).
% 4.35/1.83  tff(c_466, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 4.35/1.83  tff(c_48, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.35/1.83  tff(c_624, plain, (![B_86, A_87]: (r2_hidden(B_86, A_87) | ~m1_subset_1(B_86, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.83  tff(c_24, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.35/1.83  tff(c_631, plain, (![B_86, A_18]: (r1_tarski(B_86, A_18) | ~m1_subset_1(B_86, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_624, c_24])).
% 4.35/1.83  tff(c_831, plain, (![B_96, A_97]: (r1_tarski(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)))), inference(negUnitSimplification, [status(thm)], [c_48, c_631])).
% 4.35/1.83  tff(c_844, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_831])).
% 4.35/1.83  tff(c_1305, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.83  tff(c_1318, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1305])).
% 4.35/1.83  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/1.83  tff(c_853, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_844, c_14])).
% 4.35/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.35/1.83  tff(c_583, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/1.83  tff(c_1365, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(B_112, A_111))=k4_xboole_0(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_2, c_583])).
% 4.35/1.83  tff(c_1404, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_853, c_1365])).
% 4.35/1.83  tff(c_1442, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_1404])).
% 4.35/1.83  tff(c_133, plain, (![B_38, A_39]: (k5_xboole_0(B_38, A_39)=k5_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/1.83  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.35/1.83  tff(c_149, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_133, c_18])).
% 4.35/1.83  tff(c_854, plain, (![A_98, B_99, C_100]: (k5_xboole_0(k5_xboole_0(A_98, B_99), C_100)=k5_xboole_0(A_98, k5_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.83  tff(c_918, plain, (![A_17, C_100]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_100))=k5_xboole_0(k1_xboole_0, C_100))), inference(superposition, [status(thm), theory('equality')], [c_22, c_854])).
% 4.35/1.83  tff(c_931, plain, (![A_17, C_100]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_918])).
% 4.35/1.83  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/1.83  tff(c_948, plain, (![A_101, C_102]: (k5_xboole_0(A_101, k5_xboole_0(A_101, C_102))=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_918])).
% 4.35/1.83  tff(c_1014, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k5_xboole_0(B_104, A_103))=B_104)), inference(superposition, [status(thm), theory('equality')], [c_4, c_948])).
% 4.35/1.83  tff(c_1047, plain, (![A_17, C_100]: (k5_xboole_0(k5_xboole_0(A_17, C_100), C_100)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_931, c_1014])).
% 4.35/1.83  tff(c_1474, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1047])).
% 4.35/1.83  tff(c_465, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_59])).
% 4.35/1.83  tff(c_528, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/1.83  tff(c_538, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_465, c_528])).
% 4.35/1.83  tff(c_563, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_538])).
% 4.35/1.83  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/1.83  tff(c_2452, plain, (![B_139, A_140, B_141]: (k5_xboole_0(B_139, k5_xboole_0(A_140, B_141))=k5_xboole_0(A_140, k5_xboole_0(B_141, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_854])).
% 4.35/1.83  tff(c_2850, plain, (![A_142, B_143]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_142, B_143))=k5_xboole_0(B_143, A_142))), inference(superposition, [status(thm), theory('equality')], [c_149, c_2452])).
% 4.35/1.83  tff(c_2976, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2850])).
% 4.35/1.83  tff(c_3498, plain, (![A_148, B_149]: (k5_xboole_0(k3_xboole_0(A_148, B_149), A_148)=k4_xboole_0(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2976])).
% 4.35/1.83  tff(c_3581, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_563, c_3498])).
% 4.35/1.83  tff(c_3627, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_3581])).
% 4.35/1.83  tff(c_785, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.35/1.83  tff(c_796, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_16, c_785])).
% 4.35/1.83  tff(c_3655, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3627, c_796])).
% 4.35/1.83  tff(c_3677, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_844, c_3627, c_3655])).
% 4.35/1.83  tff(c_3679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_466, c_3677])).
% 4.35/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.83  
% 4.35/1.83  Inference rules
% 4.35/1.83  ----------------------
% 4.35/1.83  #Ref     : 0
% 4.35/1.83  #Sup     : 913
% 4.35/1.83  #Fact    : 0
% 4.35/1.83  #Define  : 0
% 4.35/1.83  #Split   : 3
% 4.35/1.83  #Chain   : 0
% 4.35/1.83  #Close   : 0
% 4.35/1.83  
% 4.35/1.83  Ordering : KBO
% 4.35/1.83  
% 4.35/1.83  Simplification rules
% 4.35/1.83  ----------------------
% 4.35/1.83  #Subsume      : 36
% 4.35/1.83  #Demod        : 881
% 4.35/1.83  #Tautology    : 622
% 4.35/1.83  #SimpNegUnit  : 7
% 4.35/1.83  #BackRed      : 2
% 4.35/1.83  
% 4.35/1.83  #Partial instantiations: 0
% 4.35/1.83  #Strategies tried      : 1
% 4.35/1.83  
% 4.35/1.83  Timing (in seconds)
% 4.35/1.83  ----------------------
% 4.35/1.84  Preprocessing        : 0.30
% 4.35/1.84  Parsing              : 0.16
% 4.35/1.84  CNF conversion       : 0.02
% 4.35/1.84  Main loop            : 0.75
% 4.35/1.84  Inferencing          : 0.22
% 4.35/1.84  Reduction            : 0.36
% 4.35/1.84  Demodulation         : 0.30
% 4.35/1.84  BG Simplification    : 0.03
% 4.35/1.84  Subsumption          : 0.10
% 4.35/1.84  Abstraction          : 0.04
% 4.35/1.84  MUC search           : 0.00
% 4.35/1.84  Cooper               : 0.00
% 4.35/1.84  Total                : 1.09
% 4.35/1.84  Index Insertion      : 0.00
% 4.35/1.84  Index Deletion       : 0.00
% 4.35/1.84  Index Matching       : 0.00
% 4.35/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
