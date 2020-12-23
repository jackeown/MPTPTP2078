%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 17.00s
% Output     : CNFRefutation 17.10s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 186 expanded)
%              Number of leaves         :   47 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 226 expanded)
%              Number of equality atoms :   66 ( 122 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_96,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_58,plain,(
    ! [A_59] : k2_subset_1(A_59) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_570,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k3_subset_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_583,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_570])).

tff(c_64,plain,(
    ! [A_64] : ~ v1_xboole_0(k1_zfmisc_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_446,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | ~ m1_subset_1(B_106,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [C_54,A_50] :
      ( r1_tarski(C_54,A_50)
      | ~ r2_hidden(C_54,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_453,plain,(
    ! [B_106,A_50] :
      ( r1_tarski(B_106,A_50)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_50))
      | v1_xboole_0(k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_446,c_36])).

tff(c_467,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_453])).

tff(c_480,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_467])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_484,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_480,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_334,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_497,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(B_114,A_113)) = k4_xboole_0(A_113,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_514,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_497])).

tff(c_585,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_514])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [B_72,A_73] : k5_xboole_0(B_72,A_73) = k5_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_18])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_353,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_334])).

tff(c_369,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_353])).

tff(c_853,plain,(
    ! [A_124,B_125,C_126] : k5_xboole_0(k5_xboole_0(A_124,B_125),C_126) = k5_xboole_0(A_124,k5_xboole_0(B_125,C_126)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_919,plain,(
    ! [A_10,C_126] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_126)) = k5_xboole_0(k1_xboole_0,C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_853])).

tff(c_967,plain,(
    ! [A_127,C_128] : k5_xboole_0(A_127,k5_xboole_0(A_127,C_128)) = C_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_919])).

tff(c_1050,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k5_xboole_0(B_130,A_129)) = B_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_967])).

tff(c_1109,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_1050])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_488,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_6])).

tff(c_491,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_488])).

tff(c_561,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_514])).

tff(c_606,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_561])).

tff(c_356,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_248,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_258,plain,(
    ! [A_93] : k3_xboole_0(k1_xboole_0,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_248])).

tff(c_267,plain,(
    ! [A_93] : k3_xboole_0(A_93,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_617,plain,(
    ! [A_117,B_118] : k5_xboole_0(k5_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_686,plain,(
    ! [A_17] : k5_xboole_0(A_17,k3_xboole_0(A_17,k1_xboole_0)) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_617])).

tff(c_715,plain,(
    ! [A_120] : k2_xboole_0(A_120,k1_xboole_0) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_267,c_686])).

tff(c_725,plain,(
    ! [A_120] : k3_xboole_0(A_120,A_120) = A_120 ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_10])).

tff(c_1654,plain,(
    ! [A_143,B_144,C_145] : k5_xboole_0(k3_xboole_0(A_143,B_144),k3_xboole_0(C_145,B_144)) = k3_xboole_0(k5_xboole_0(A_143,C_145),B_144) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1695,plain,(
    ! [A_120,C_145] : k5_xboole_0(A_120,k3_xboole_0(C_145,A_120)) = k3_xboole_0(k5_xboole_0(A_120,C_145),A_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_1654])).

tff(c_2853,plain,(
    ! [A_172,C_173] : k3_xboole_0(A_172,k5_xboole_0(A_172,C_173)) = k4_xboole_0(A_172,C_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_2,c_1695])).

tff(c_2956,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_2853])).

tff(c_3002,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_2956])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3182,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3002,c_22])).

tff(c_3193,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1109,c_3182])).

tff(c_62,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k3_subset_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4355,plain,(
    ! [A_201,B_202,C_203] :
      ( k4_subset_1(A_201,B_202,C_203) = k2_xboole_0(B_202,C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46134,plain,(
    ! [A_477,B_478,B_479] :
      ( k4_subset_1(A_477,B_478,k3_subset_1(A_477,B_479)) = k2_xboole_0(B_478,k3_subset_1(A_477,B_479))
      | ~ m1_subset_1(B_478,k1_zfmisc_1(A_477))
      | ~ m1_subset_1(B_479,k1_zfmisc_1(A_477)) ) ),
    inference(resolution,[status(thm)],[c_62,c_4355])).

tff(c_46535,plain,(
    ! [B_481] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_481)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_481))
      | ~ m1_subset_1(B_481,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_70,c_46134])).

tff(c_46558,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_46535])).

tff(c_46570,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3193,c_46558])).

tff(c_46572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_46570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.00/9.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.00/9.70  
% 17.00/9.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.00/9.70  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 17.00/9.70  
% 17.00/9.70  %Foreground sorts:
% 17.00/9.70  
% 17.00/9.70  
% 17.00/9.70  %Background operators:
% 17.00/9.70  
% 17.00/9.70  
% 17.00/9.70  %Foreground operators:
% 17.00/9.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.00/9.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.00/9.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.00/9.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.00/9.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.00/9.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.00/9.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.00/9.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.00/9.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.00/9.70  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.00/9.70  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.00/9.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.00/9.70  tff('#skF_3', type, '#skF_3': $i).
% 17.00/9.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.00/9.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.00/9.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.00/9.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.00/9.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.00/9.70  tff('#skF_4', type, '#skF_4': $i).
% 17.00/9.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.00/9.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.00/9.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.00/9.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.00/9.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.00/9.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.00/9.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.00/9.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.00/9.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.00/9.70  
% 17.10/9.72  tff(f_85, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 17.10/9.72  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 17.10/9.72  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 17.10/9.72  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.10/9.72  tff(f_96, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 17.10/9.72  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 17.10/9.72  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.10/9.72  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.10/9.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.10/9.72  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.10/9.72  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 17.10/9.72  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 17.10/9.72  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 17.10/9.72  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 17.10/9.72  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.10/9.72  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 17.10/9.72  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 17.10/9.72  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.10/9.72  tff(f_102, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.10/9.72  tff(c_58, plain, (![A_59]: (k2_subset_1(A_59)=A_59)), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.10/9.72  tff(c_68, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.10/9.72  tff(c_71, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68])).
% 17.10/9.72  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.10/9.72  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.10/9.72  tff(c_570, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k3_subset_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.10/9.72  tff(c_583, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_570])).
% 17.10/9.72  tff(c_64, plain, (![A_64]: (~v1_xboole_0(k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.10/9.72  tff(c_446, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | ~m1_subset_1(B_106, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.10/9.72  tff(c_36, plain, (![C_54, A_50]: (r1_tarski(C_54, A_50) | ~r2_hidden(C_54, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.10/9.72  tff(c_453, plain, (![B_106, A_50]: (r1_tarski(B_106, A_50) | ~m1_subset_1(B_106, k1_zfmisc_1(A_50)) | v1_xboole_0(k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_446, c_36])).
% 17.10/9.72  tff(c_467, plain, (![B_111, A_112]: (r1_tarski(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(negUnitSimplification, [status(thm)], [c_64, c_453])).
% 17.10/9.72  tff(c_480, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_467])).
% 17.10/9.72  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.10/9.72  tff(c_484, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_480, c_12])).
% 17.10/9.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.10/9.72  tff(c_334, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.10/9.72  tff(c_497, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(B_114, A_113))=k4_xboole_0(A_113, B_114))), inference(superposition, [status(thm), theory('equality')], [c_2, c_334])).
% 17.10/9.72  tff(c_514, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_484, c_497])).
% 17.10/9.72  tff(c_585, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_583, c_514])).
% 17.10/9.72  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.10/9.72  tff(c_92, plain, (![B_72, A_73]: (k5_xboole_0(B_72, A_73)=k5_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.10/9.72  tff(c_108, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_92, c_18])).
% 17.10/9.72  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.10/9.72  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.10/9.72  tff(c_353, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_334])).
% 17.10/9.72  tff(c_369, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_353])).
% 17.10/9.72  tff(c_853, plain, (![A_124, B_125, C_126]: (k5_xboole_0(k5_xboole_0(A_124, B_125), C_126)=k5_xboole_0(A_124, k5_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.10/9.72  tff(c_919, plain, (![A_10, C_126]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_126))=k5_xboole_0(k1_xboole_0, C_126))), inference(superposition, [status(thm), theory('equality')], [c_369, c_853])).
% 17.10/9.72  tff(c_967, plain, (![A_127, C_128]: (k5_xboole_0(A_127, k5_xboole_0(A_127, C_128))=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_919])).
% 17.10/9.72  tff(c_1050, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k5_xboole_0(B_130, A_129))=B_130)), inference(superposition, [status(thm), theory('equality')], [c_4, c_967])).
% 17.10/9.72  tff(c_1109, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_585, c_1050])).
% 17.10/9.72  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.10/9.72  tff(c_488, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_484, c_6])).
% 17.10/9.72  tff(c_491, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_369, c_488])).
% 17.10/9.72  tff(c_561, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_514])).
% 17.10/9.72  tff(c_606, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_583, c_561])).
% 17.10/9.72  tff(c_356, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_334])).
% 17.10/9.72  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.10/9.72  tff(c_248, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.10/9.72  tff(c_258, plain, (![A_93]: (k3_xboole_0(k1_xboole_0, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_248])).
% 17.10/9.72  tff(c_267, plain, (![A_93]: (k3_xboole_0(A_93, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_2])).
% 17.10/9.72  tff(c_617, plain, (![A_117, B_118]: (k5_xboole_0(k5_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.10/9.72  tff(c_686, plain, (![A_17]: (k5_xboole_0(A_17, k3_xboole_0(A_17, k1_xboole_0))=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_617])).
% 17.10/9.72  tff(c_715, plain, (![A_120]: (k2_xboole_0(A_120, k1_xboole_0)=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_267, c_686])).
% 17.10/9.72  tff(c_725, plain, (![A_120]: (k3_xboole_0(A_120, A_120)=A_120)), inference(superposition, [status(thm), theory('equality')], [c_715, c_10])).
% 17.10/9.72  tff(c_1654, plain, (![A_143, B_144, C_145]: (k5_xboole_0(k3_xboole_0(A_143, B_144), k3_xboole_0(C_145, B_144))=k3_xboole_0(k5_xboole_0(A_143, C_145), B_144))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.10/9.72  tff(c_1695, plain, (![A_120, C_145]: (k5_xboole_0(A_120, k3_xboole_0(C_145, A_120))=k3_xboole_0(k5_xboole_0(A_120, C_145), A_120))), inference(superposition, [status(thm), theory('equality')], [c_725, c_1654])).
% 17.10/9.72  tff(c_2853, plain, (![A_172, C_173]: (k3_xboole_0(A_172, k5_xboole_0(A_172, C_173))=k4_xboole_0(A_172, C_173))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_2, c_1695])).
% 17.10/9.72  tff(c_2956, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_606, c_2853])).
% 17.10/9.72  tff(c_3002, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_491, c_2956])).
% 17.10/9.72  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.10/9.72  tff(c_3182, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3002, c_22])).
% 17.10/9.72  tff(c_3193, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1109, c_3182])).
% 17.10/9.72  tff(c_62, plain, (![A_62, B_63]: (m1_subset_1(k3_subset_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.10/9.72  tff(c_4355, plain, (![A_201, B_202, C_203]: (k4_subset_1(A_201, B_202, C_203)=k2_xboole_0(B_202, C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(A_201)) | ~m1_subset_1(B_202, k1_zfmisc_1(A_201)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 17.10/9.72  tff(c_46134, plain, (![A_477, B_478, B_479]: (k4_subset_1(A_477, B_478, k3_subset_1(A_477, B_479))=k2_xboole_0(B_478, k3_subset_1(A_477, B_479)) | ~m1_subset_1(B_478, k1_zfmisc_1(A_477)) | ~m1_subset_1(B_479, k1_zfmisc_1(A_477)))), inference(resolution, [status(thm)], [c_62, c_4355])).
% 17.10/9.72  tff(c_46535, plain, (![B_481]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_481))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_481)) | ~m1_subset_1(B_481, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_70, c_46134])).
% 17.10/9.72  tff(c_46558, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_46535])).
% 17.10/9.72  tff(c_46570, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3193, c_46558])).
% 17.10/9.72  tff(c_46572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_46570])).
% 17.10/9.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.10/9.72  
% 17.10/9.72  Inference rules
% 17.10/9.72  ----------------------
% 17.10/9.72  #Ref     : 0
% 17.10/9.72  #Sup     : 11799
% 17.10/9.72  #Fact    : 0
% 17.10/9.72  #Define  : 0
% 17.10/9.72  #Split   : 0
% 17.10/9.72  #Chain   : 0
% 17.10/9.72  #Close   : 0
% 17.10/9.72  
% 17.10/9.72  Ordering : KBO
% 17.10/9.72  
% 17.10/9.72  Simplification rules
% 17.10/9.72  ----------------------
% 17.10/9.72  #Subsume      : 299
% 17.10/9.72  #Demod        : 16683
% 17.10/9.72  #Tautology    : 5945
% 17.10/9.72  #SimpNegUnit  : 22
% 17.10/9.72  #BackRed      : 4
% 17.10/9.72  
% 17.10/9.72  #Partial instantiations: 0
% 17.10/9.72  #Strategies tried      : 1
% 17.10/9.72  
% 17.10/9.72  Timing (in seconds)
% 17.10/9.72  ----------------------
% 17.10/9.72  Preprocessing        : 0.34
% 17.10/9.72  Parsing              : 0.18
% 17.10/9.72  CNF conversion       : 0.02
% 17.10/9.72  Main loop            : 8.63
% 17.10/9.72  Inferencing          : 1.05
% 17.10/9.72  Reduction            : 5.76
% 17.10/9.72  Demodulation         : 5.35
% 17.10/9.72  BG Simplification    : 0.16
% 17.10/9.72  Subsumption          : 1.36
% 17.10/9.72  Abstraction          : 0.27
% 17.10/9.72  MUC search           : 0.00
% 17.10/9.72  Cooper               : 0.00
% 17.10/9.72  Total                : 9.01
% 17.10/9.72  Index Insertion      : 0.00
% 17.10/9.72  Index Deletion       : 0.00
% 17.10/9.72  Index Matching       : 0.00
% 17.10/9.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
