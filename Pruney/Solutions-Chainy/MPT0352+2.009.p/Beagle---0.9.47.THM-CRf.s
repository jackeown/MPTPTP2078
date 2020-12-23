%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 186 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 301 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_94,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_60,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_171,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_191,plain,(
    ! [A_14] : k2_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_18,c_171])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1414,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski(A_120,k2_xboole_0(B_121,C_122))
      | ~ r1_tarski(k4_xboole_0(A_120,B_121),C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1964,plain,(
    ! [A_137,B_138] : r1_tarski(A_137,k2_xboole_0(B_138,k4_xboole_0(A_137,B_138))) ),
    inference(resolution,[status(thm)],[c_10,c_1414])).

tff(c_2011,plain,(
    ! [A_139] : r1_tarski(A_139,k4_xboole_0(A_139,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1964])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2019,plain,(
    ! [A_139] :
      ( k4_xboole_0(A_139,k1_xboole_0) = A_139
      | ~ r1_tarski(k4_xboole_0(A_139,k1_xboole_0),A_139) ) ),
    inference(resolution,[status(thm)],[c_2011,c_6])).

tff(c_2031,plain,(
    ! [A_139] : k4_xboole_0(A_139,k1_xboole_0) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2019])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_783,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,A_93)
      | ~ m1_subset_1(B_92,A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [C_34,A_30] :
      ( r1_tarski(C_34,A_30)
      | ~ r2_hidden(C_34,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_790,plain,(
    ! [B_92,A_30] :
      ( r1_tarski(B_92,A_30)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_783,c_32])).

tff(c_936,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_790])).

tff(c_953,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_936])).

tff(c_209,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(resolution,[status(thm)],[c_18,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_222,plain,(
    ! [A_63] : k2_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2])).

tff(c_1339,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(k4_xboole_0(A_115,B_116),C_117)
      | ~ r1_tarski(A_115,k2_xboole_0(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_856,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_883,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_856])).

tff(c_1352,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k1_xboole_0
      | ~ r1_tarski(A_115,k2_xboole_0(B_116,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1339,c_883])).

tff(c_2348,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k1_xboole_0
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1352])).

tff(c_2435,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_953,c_2348])).

tff(c_28,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2475,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_28])).

tff(c_2492,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_2475])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1052,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1069,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1052])).

tff(c_1099,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_28])).

tff(c_1111,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1099])).

tff(c_18785,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_1111])).

tff(c_66,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_250,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_66])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1068,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1052])).

tff(c_5190,plain,(
    ! [C_186] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_186))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_1414])).

tff(c_5227,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_250,c_5190])).

tff(c_188,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_22,c_171])).

tff(c_1105,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_188])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8927,plain,(
    ! [A_238,B_239,C_240] :
      ( k2_xboole_0(k4_xboole_0(A_238,B_239),C_240) = C_240
      | ~ r1_tarski(A_238,k2_xboole_0(B_239,C_240)) ) ),
    inference(resolution,[status(thm)],[c_1339,c_14])).

tff(c_22825,plain,(
    ! [B_443,C_444] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_443,C_444),B_443),C_444) = C_444 ),
    inference(resolution,[status(thm)],[c_10,c_8927])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_23257,plain,(
    ! [B_445,C_446] : r1_tarski(k4_xboole_0(k2_xboole_0(B_445,C_446),B_445),C_446) ),
    inference(superposition,[status(thm),theory(equality)],[c_22825,c_30])).

tff(c_952,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_936])).

tff(c_968,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_tarski(A_102,C_103)
      | ~ r1_tarski(B_104,C_103)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_990,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,'#skF_3')
      | ~ r1_tarski(A_102,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_952,c_968])).

tff(c_23534,plain,(
    ! [B_447] : r1_tarski(k4_xboole_0(k2_xboole_0(B_447,'#skF_5'),B_447),'#skF_3') ),
    inference(resolution,[status(thm)],[c_23257,c_990])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_23958,plain,(
    ! [B_451] : r1_tarski(k2_xboole_0(B_451,'#skF_5'),k2_xboole_0(B_451,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_23534,c_26])).

tff(c_24003,plain,(
    r1_tarski(k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_23958])).

tff(c_24083,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24003])).

tff(c_24957,plain,
    ( k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_24083,c_6])).

tff(c_24965,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5227,c_24957])).

tff(c_23461,plain,(
    ! [B_2,A_1] : r1_tarski(k4_xboole_0(k2_xboole_0(B_2,A_1),A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_23257])).

tff(c_24983,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24965,c_23461])).

tff(c_25072,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18785,c_24983])).

tff(c_25074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_25072])).

tff(c_25075,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_25076,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_25707,plain,(
    ! [A_500,B_501] :
      ( k4_xboole_0(A_500,B_501) = k3_subset_1(A_500,B_501)
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_500)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_25719,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_25707])).

tff(c_25720,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_25707])).

tff(c_26075,plain,(
    ! [C_512,B_513,A_514] :
      ( r1_tarski(k4_xboole_0(C_512,B_513),k4_xboole_0(C_512,A_514))
      | ~ r1_tarski(A_514,B_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26901,plain,(
    ! [B_544] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_544),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25720,c_26075])).

tff(c_26920,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25719,c_26901])).

tff(c_26933,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25076,c_26920])).

tff(c_26935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25075,c_26933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.49/4.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/4.66  
% 11.49/4.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/4.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.49/4.66  
% 11.49/4.66  %Foreground sorts:
% 11.49/4.66  
% 11.49/4.66  
% 11.49/4.66  %Background operators:
% 11.49/4.66  
% 11.49/4.66  
% 11.49/4.66  %Foreground operators:
% 11.49/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.49/4.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.49/4.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.49/4.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.49/4.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.49/4.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.49/4.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.49/4.66  tff('#skF_5', type, '#skF_5': $i).
% 11.49/4.66  tff('#skF_3', type, '#skF_3': $i).
% 11.49/4.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.49/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.49/4.66  tff('#skF_4', type, '#skF_4': $i).
% 11.49/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.49/4.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.49/4.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.49/4.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.49/4.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.49/4.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.49/4.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.49/4.66  
% 11.63/4.68  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 11.63/4.68  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.63/4.68  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.63/4.68  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.63/4.68  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.63/4.68  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.63/4.68  tff(f_94, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.63/4.68  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.63/4.68  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.63/4.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.63/4.68  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.63/4.68  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.63/4.68  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.63/4.68  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.63/4.68  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.63/4.68  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.63/4.68  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 11.63/4.68  tff(c_60, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.63/4.68  tff(c_145, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 11.63/4.68  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.63/4.68  tff(c_18, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.63/4.68  tff(c_171, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.63/4.68  tff(c_191, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14)), inference(resolution, [status(thm)], [c_18, c_171])).
% 11.63/4.68  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.63/4.68  tff(c_1414, plain, (![A_120, B_121, C_122]: (r1_tarski(A_120, k2_xboole_0(B_121, C_122)) | ~r1_tarski(k4_xboole_0(A_120, B_121), C_122))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.63/4.68  tff(c_1964, plain, (![A_137, B_138]: (r1_tarski(A_137, k2_xboole_0(B_138, k4_xboole_0(A_137, B_138))))), inference(resolution, [status(thm)], [c_10, c_1414])).
% 11.63/4.68  tff(c_2011, plain, (![A_139]: (r1_tarski(A_139, k4_xboole_0(A_139, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_1964])).
% 11.63/4.68  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.63/4.68  tff(c_2019, plain, (![A_139]: (k4_xboole_0(A_139, k1_xboole_0)=A_139 | ~r1_tarski(k4_xboole_0(A_139, k1_xboole_0), A_139))), inference(resolution, [status(thm)], [c_2011, c_6])).
% 11.63/4.68  tff(c_2031, plain, (![A_139]: (k4_xboole_0(A_139, k1_xboole_0)=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2019])).
% 11.63/4.68  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.63/4.68  tff(c_54, plain, (![A_39]: (~v1_xboole_0(k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.63/4.68  tff(c_783, plain, (![B_92, A_93]: (r2_hidden(B_92, A_93) | ~m1_subset_1(B_92, A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.63/4.68  tff(c_32, plain, (![C_34, A_30]: (r1_tarski(C_34, A_30) | ~r2_hidden(C_34, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.63/4.68  tff(c_790, plain, (![B_92, A_30]: (r1_tarski(B_92, A_30) | ~m1_subset_1(B_92, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_783, c_32])).
% 11.63/4.68  tff(c_936, plain, (![B_100, A_101]: (r1_tarski(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)))), inference(negUnitSimplification, [status(thm)], [c_54, c_790])).
% 11.63/4.68  tff(c_953, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_936])).
% 11.63/4.68  tff(c_209, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(resolution, [status(thm)], [c_18, c_171])).
% 11.63/4.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.63/4.68  tff(c_222, plain, (![A_63]: (k2_xboole_0(A_63, k1_xboole_0)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_209, c_2])).
% 11.63/4.68  tff(c_1339, plain, (![A_115, B_116, C_117]: (r1_tarski(k4_xboole_0(A_115, B_116), C_117) | ~r1_tarski(A_115, k2_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.63/4.68  tff(c_856, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.63/4.68  tff(c_883, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_856])).
% 11.63/4.68  tff(c_1352, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k1_xboole_0 | ~r1_tarski(A_115, k2_xboole_0(B_116, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1339, c_883])).
% 11.63/4.68  tff(c_2348, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k1_xboole_0 | ~r1_tarski(A_147, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1352])).
% 11.63/4.68  tff(c_2435, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_953, c_2348])).
% 11.63/4.68  tff(c_28, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.63/4.68  tff(c_2475, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2435, c_28])).
% 11.63/4.68  tff(c_2492, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_2475])).
% 11.63/4.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.63/4.68  tff(c_1052, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.63/4.68  tff(c_1069, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1052])).
% 11.63/4.68  tff(c_1099, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1069, c_28])).
% 11.63/4.68  tff(c_1111, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1099])).
% 11.63/4.68  tff(c_18785, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_1111])).
% 11.63/4.68  tff(c_66, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.63/4.68  tff(c_250, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_145, c_66])).
% 11.63/4.68  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.63/4.68  tff(c_1068, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_1052])).
% 11.63/4.68  tff(c_5190, plain, (![C_186]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_186)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_186))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_1414])).
% 11.63/4.68  tff(c_5227, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_250, c_5190])).
% 11.63/4.68  tff(c_188, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), A_18)=A_18)), inference(resolution, [status(thm)], [c_22, c_171])).
% 11.63/4.68  tff(c_1105, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1069, c_188])).
% 11.63/4.68  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.63/4.68  tff(c_8927, plain, (![A_238, B_239, C_240]: (k2_xboole_0(k4_xboole_0(A_238, B_239), C_240)=C_240 | ~r1_tarski(A_238, k2_xboole_0(B_239, C_240)))), inference(resolution, [status(thm)], [c_1339, c_14])).
% 11.63/4.68  tff(c_22825, plain, (![B_443, C_444]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_443, C_444), B_443), C_444)=C_444)), inference(resolution, [status(thm)], [c_10, c_8927])).
% 11.63/4.68  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.63/4.68  tff(c_23257, plain, (![B_445, C_446]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_445, C_446), B_445), C_446))), inference(superposition, [status(thm), theory('equality')], [c_22825, c_30])).
% 11.63/4.68  tff(c_952, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_936])).
% 11.63/4.68  tff(c_968, plain, (![A_102, C_103, B_104]: (r1_tarski(A_102, C_103) | ~r1_tarski(B_104, C_103) | ~r1_tarski(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.63/4.68  tff(c_990, plain, (![A_102]: (r1_tarski(A_102, '#skF_3') | ~r1_tarski(A_102, '#skF_5'))), inference(resolution, [status(thm)], [c_952, c_968])).
% 11.63/4.68  tff(c_23534, plain, (![B_447]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_447, '#skF_5'), B_447), '#skF_3'))), inference(resolution, [status(thm)], [c_23257, c_990])).
% 11.63/4.68  tff(c_26, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.63/4.68  tff(c_23958, plain, (![B_451]: (r1_tarski(k2_xboole_0(B_451, '#skF_5'), k2_xboole_0(B_451, '#skF_3')))), inference(resolution, [status(thm)], [c_23534, c_26])).
% 11.63/4.68  tff(c_24003, plain, (r1_tarski(k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1105, c_23958])).
% 11.63/4.68  tff(c_24083, plain, (r1_tarski(k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24003])).
% 11.63/4.68  tff(c_24957, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_24083, c_6])).
% 11.63/4.68  tff(c_24965, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5227, c_24957])).
% 11.63/4.68  tff(c_23461, plain, (![B_2, A_1]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_2, A_1), A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_23257])).
% 11.63/4.68  tff(c_24983, plain, (r1_tarski(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24965, c_23461])).
% 11.63/4.68  tff(c_25072, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18785, c_24983])).
% 11.63/4.68  tff(c_25074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_25072])).
% 11.63/4.68  tff(c_25075, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 11.63/4.68  tff(c_25076, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 11.63/4.68  tff(c_25707, plain, (![A_500, B_501]: (k4_xboole_0(A_500, B_501)=k3_subset_1(A_500, B_501) | ~m1_subset_1(B_501, k1_zfmisc_1(A_500)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.63/4.68  tff(c_25719, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_25707])).
% 11.63/4.68  tff(c_25720, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_25707])).
% 11.63/4.68  tff(c_26075, plain, (![C_512, B_513, A_514]: (r1_tarski(k4_xboole_0(C_512, B_513), k4_xboole_0(C_512, A_514)) | ~r1_tarski(A_514, B_513))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.63/4.68  tff(c_26901, plain, (![B_544]: (r1_tarski(k4_xboole_0('#skF_3', B_544), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_544))), inference(superposition, [status(thm), theory('equality')], [c_25720, c_26075])).
% 11.63/4.68  tff(c_26920, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25719, c_26901])).
% 11.63/4.68  tff(c_26933, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_25076, c_26920])).
% 11.63/4.68  tff(c_26935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25075, c_26933])).
% 11.63/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.68  
% 11.63/4.68  Inference rules
% 11.63/4.68  ----------------------
% 11.63/4.68  #Ref     : 0
% 11.63/4.68  #Sup     : 6592
% 11.63/4.68  #Fact    : 0
% 11.63/4.68  #Define  : 0
% 11.63/4.68  #Split   : 10
% 11.63/4.68  #Chain   : 0
% 11.63/4.68  #Close   : 0
% 11.63/4.68  
% 11.63/4.68  Ordering : KBO
% 11.63/4.68  
% 11.63/4.68  Simplification rules
% 11.63/4.68  ----------------------
% 11.63/4.68  #Subsume      : 344
% 11.63/4.68  #Demod        : 5102
% 11.63/4.68  #Tautology    : 4079
% 11.63/4.68  #SimpNegUnit  : 23
% 11.63/4.68  #BackRed      : 6
% 11.63/4.68  
% 11.63/4.68  #Partial instantiations: 0
% 11.63/4.68  #Strategies tried      : 1
% 11.63/4.68  
% 11.63/4.68  Timing (in seconds)
% 11.63/4.68  ----------------------
% 11.63/4.68  Preprocessing        : 0.32
% 11.63/4.68  Parsing              : 0.17
% 11.63/4.68  CNF conversion       : 0.02
% 11.63/4.68  Main loop            : 3.59
% 11.63/4.68  Inferencing          : 0.68
% 11.63/4.68  Reduction            : 1.86
% 11.63/4.68  Demodulation         : 1.59
% 11.63/4.68  BG Simplification    : 0.07
% 11.63/4.68  Subsumption          : 0.76
% 11.63/4.68  Abstraction          : 0.09
% 11.63/4.68  MUC search           : 0.00
% 11.63/4.68  Cooper               : 0.00
% 11.63/4.68  Total                : 3.95
% 11.63/4.68  Index Insertion      : 0.00
% 11.63/4.68  Index Deletion       : 0.00
% 11.63/4.68  Index Matching       : 0.00
% 11.63/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
