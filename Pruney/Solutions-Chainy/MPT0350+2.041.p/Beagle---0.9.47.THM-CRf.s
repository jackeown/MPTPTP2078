%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:31 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 316 expanded)
%              Number of leaves         :   43 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  117 ( 367 expanded)
%              Number of equality atoms :   73 ( 254 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_50,plain,(
    ! [A_39] : k2_subset_1(A_39) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_63,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1384,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k3_subset_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1401,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1384])).

tff(c_56,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_309,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_316,plain,(
    ! [B_85,A_27] :
      ( r1_tarski(B_85,A_27)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_309,c_26])).

tff(c_321,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_316])).

tff(c_334,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_321])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_338,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_334,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_244,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,k3_xboole_0(A_90,B_89)) = k4_xboole_0(B_89,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_244])).

tff(c_383,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_370])).

tff(c_1404,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_383])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_259,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_244])).

tff(c_262,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_259])).

tff(c_455,plain,(
    ! [A_96,B_97,C_98] : k5_xboole_0(k5_xboole_0(A_96,B_97),C_98) = k5_xboole_0(A_96,k5_xboole_0(B_97,C_98)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_957,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = k5_xboole_0(k1_xboole_0,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_455])).

tff(c_1064,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k5_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_957])).

tff(c_1096,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1064])).

tff(c_507,plain,(
    ! [A_3,C_98] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_98)) = k5_xboole_0(k1_xboole_0,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_455])).

tff(c_1098,plain,(
    ! [A_3,C_98] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_98)) = C_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_507])).

tff(c_1557,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_1098])).

tff(c_473,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k5_xboole_0(B_97,k5_xboole_0(A_96,B_97))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_262])).

tff(c_1193,plain,(
    ! [A_111,C_112] : k5_xboole_0(A_111,k5_xboole_0(A_111,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_507])).

tff(c_1244,plain,(
    ! [B_97,A_96] : k5_xboole_0(B_97,k5_xboole_0(A_96,B_97)) = k5_xboole_0(A_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_1193])).

tff(c_1298,plain,(
    ! [B_97,A_96] : k5_xboole_0(B_97,k5_xboole_0(A_96,B_97)) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1244])).

tff(c_2235,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_1298])).

tff(c_20,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_661,plain,(
    ! [C_102] : k5_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_102) = k5_xboole_0('#skF_3',k5_xboole_0('#skF_4',C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_455])).

tff(c_683,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_262])).

tff(c_722,plain,(
    k5_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_683])).

tff(c_1251,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_1193])).

tff(c_1300,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1251])).

tff(c_1408,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1401,c_20])).

tff(c_1411,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_1408])).

tff(c_256,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_244])).

tff(c_1685,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k3_xboole_0(A_122,B_123),k3_xboole_0(C_124,B_123)) = k3_xboole_0(k5_xboole_0(A_122,C_124),B_123) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1749,plain,(
    ! [A_3,C_124] : k5_xboole_0(A_3,k3_xboole_0(C_124,A_3)) = k3_xboole_0(k5_xboole_0(A_3,C_124),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1685])).

tff(c_2686,plain,(
    ! [A_149,C_150] : k3_xboole_0(A_149,k5_xboole_0(A_149,C_150)) = k4_xboole_0(A_149,C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2,c_1749])).

tff(c_2760,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_2686])).

tff(c_2797,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_2760])).

tff(c_2931,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2797,c_20])).

tff(c_2935,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_2931])).

tff(c_54,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k3_subset_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2670,plain,(
    ! [A_146,B_147,C_148] :
      ( k4_subset_1(A_146,B_147,C_148) = k2_xboole_0(B_147,C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2801,plain,(
    ! [B_151] :
      ( k4_subset_1('#skF_3',B_151,'#skF_4') = k2_xboole_0(B_151,'#skF_4')
      | ~ m1_subset_1(B_151,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_2670])).

tff(c_4259,plain,(
    ! [B_184] :
      ( k4_subset_1('#skF_3',k3_subset_1('#skF_3',B_184),'#skF_4') = k2_xboole_0(k3_subset_1('#skF_3',B_184),'#skF_4')
      | ~ m1_subset_1(B_184,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2801])).

tff(c_4274,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4259])).

tff(c_4279,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2935,c_4274])).

tff(c_2911,plain,(
    ! [A_154,C_155,B_156] :
      ( k4_subset_1(A_154,C_155,B_156) = k4_subset_1(A_154,B_156,C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2977,plain,(
    ! [B_157] :
      ( k4_subset_1('#skF_3',B_157,'#skF_4') = k4_subset_1('#skF_3','#skF_4',B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_2911])).

tff(c_4696,plain,(
    ! [B_190] :
      ( k4_subset_1('#skF_3',k3_subset_1('#skF_3',B_190),'#skF_4') = k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2977])).

tff(c_4711,plain,(
    k4_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_4696])).

tff(c_4716,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4279,c_4711])).

tff(c_4718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_4716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:21:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.89  
% 4.77/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.90  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.77/1.90  
% 4.77/1.90  %Foreground sorts:
% 4.77/1.90  
% 4.77/1.90  
% 4.77/1.90  %Background operators:
% 4.77/1.90  
% 4.77/1.90  
% 4.77/1.90  %Foreground operators:
% 4.77/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.77/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.77/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.77/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.77/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.77/1.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.77/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.77/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.77/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.77/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.77/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.77/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.90  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.77/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.77/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.90  
% 4.77/1.91  tff(f_81, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.77/1.91  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 4.77/1.91  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.77/1.91  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.77/1.91  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.77/1.91  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.77/1.91  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.77/1.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.77/1.91  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.77/1.91  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.77/1.91  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.77/1.91  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.77/1.91  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.77/1.91  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.77/1.91  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.77/1.91  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.77/1.91  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.77/1.91  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.77/1.91  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 4.77/1.91  tff(c_50, plain, (![A_39]: (k2_subset_1(A_39)=A_39)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.77/1.91  tff(c_60, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.77/1.91  tff(c_63, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60])).
% 4.77/1.91  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.77/1.91  tff(c_1384, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k3_subset_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.91  tff(c_1401, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_1384])).
% 4.77/1.91  tff(c_56, plain, (![A_44]: (~v1_xboole_0(k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.77/1.91  tff(c_309, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.77/1.91  tff(c_26, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.77/1.91  tff(c_316, plain, (![B_85, A_27]: (r1_tarski(B_85, A_27) | ~m1_subset_1(B_85, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_309, c_26])).
% 4.77/1.91  tff(c_321, plain, (![B_87, A_88]: (r1_tarski(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_56, c_316])).
% 4.77/1.91  tff(c_334, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_321])).
% 4.77/1.91  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/1.91  tff(c_338, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_334, c_12])).
% 4.77/1.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.77/1.91  tff(c_244, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.91  tff(c_370, plain, (![B_89, A_90]: (k5_xboole_0(B_89, k3_xboole_0(A_90, B_89))=k4_xboole_0(B_89, A_90))), inference(superposition, [status(thm), theory('equality')], [c_2, c_244])).
% 4.77/1.91  tff(c_383, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_338, c_370])).
% 4.77/1.91  tff(c_1404, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_383])).
% 4.77/1.91  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.91  tff(c_132, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k3_xboole_0(A_56, B_57))=A_56)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.91  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.77/1.91  tff(c_138, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_14])).
% 4.77/1.91  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.77/1.91  tff(c_259, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_244])).
% 4.77/1.91  tff(c_262, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_259])).
% 4.77/1.91  tff(c_455, plain, (![A_96, B_97, C_98]: (k5_xboole_0(k5_xboole_0(A_96, B_97), C_98)=k5_xboole_0(A_96, k5_xboole_0(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.77/1.91  tff(c_957, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=k5_xboole_0(k1_xboole_0, C_109))), inference(superposition, [status(thm), theory('equality')], [c_262, c_455])).
% 4.77/1.91  tff(c_1064, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k5_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_262, c_957])).
% 4.77/1.91  tff(c_1096, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1064])).
% 4.77/1.91  tff(c_507, plain, (![A_3, C_98]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_98))=k5_xboole_0(k1_xboole_0, C_98))), inference(superposition, [status(thm), theory('equality')], [c_262, c_455])).
% 4.77/1.91  tff(c_1098, plain, (![A_3, C_98]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_98))=C_98)), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_507])).
% 4.77/1.91  tff(c_1557, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1404, c_1098])).
% 4.77/1.91  tff(c_473, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k5_xboole_0(B_97, k5_xboole_0(A_96, B_97)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_455, c_262])).
% 4.77/1.91  tff(c_1193, plain, (![A_111, C_112]: (k5_xboole_0(A_111, k5_xboole_0(A_111, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_507])).
% 4.77/1.91  tff(c_1244, plain, (![B_97, A_96]: (k5_xboole_0(B_97, k5_xboole_0(A_96, B_97))=k5_xboole_0(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_473, c_1193])).
% 4.77/1.91  tff(c_1298, plain, (![B_97, A_96]: (k5_xboole_0(B_97, k5_xboole_0(A_96, B_97))=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1244])).
% 4.77/1.91  tff(c_2235, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1557, c_1298])).
% 4.77/1.91  tff(c_20, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.77/1.91  tff(c_661, plain, (![C_102]: (k5_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_102)=k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', C_102)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_455])).
% 4.77/1.91  tff(c_683, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_661, c_262])).
% 4.77/1.91  tff(c_722, plain, (k5_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_683])).
% 4.77/1.91  tff(c_1251, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_722, c_1193])).
% 4.77/1.91  tff(c_1300, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1251])).
% 4.77/1.91  tff(c_1408, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1401, c_20])).
% 4.77/1.91  tff(c_1411, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_1408])).
% 4.77/1.91  tff(c_256, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_244])).
% 4.77/1.91  tff(c_1685, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k3_xboole_0(A_122, B_123), k3_xboole_0(C_124, B_123))=k3_xboole_0(k5_xboole_0(A_122, C_124), B_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/1.91  tff(c_1749, plain, (![A_3, C_124]: (k5_xboole_0(A_3, k3_xboole_0(C_124, A_3))=k3_xboole_0(k5_xboole_0(A_3, C_124), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1685])).
% 4.77/1.91  tff(c_2686, plain, (![A_149, C_150]: (k3_xboole_0(A_149, k5_xboole_0(A_149, C_150))=k4_xboole_0(A_149, C_150))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2, c_1749])).
% 4.77/1.91  tff(c_2760, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_2686])).
% 4.77/1.91  tff(c_2797, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_2760])).
% 4.77/1.91  tff(c_2931, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2797, c_20])).
% 4.77/1.91  tff(c_2935, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2235, c_2931])).
% 4.77/1.91  tff(c_54, plain, (![A_42, B_43]: (m1_subset_1(k3_subset_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.91  tff(c_2670, plain, (![A_146, B_147, C_148]: (k4_subset_1(A_146, B_147, C_148)=k2_xboole_0(B_147, C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.77/1.91  tff(c_2801, plain, (![B_151]: (k4_subset_1('#skF_3', B_151, '#skF_4')=k2_xboole_0(B_151, '#skF_4') | ~m1_subset_1(B_151, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_2670])).
% 4.77/1.91  tff(c_4259, plain, (![B_184]: (k4_subset_1('#skF_3', k3_subset_1('#skF_3', B_184), '#skF_4')=k2_xboole_0(k3_subset_1('#skF_3', B_184), '#skF_4') | ~m1_subset_1(B_184, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_2801])).
% 4.77/1.91  tff(c_4274, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_62, c_4259])).
% 4.77/1.91  tff(c_4279, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2935, c_4274])).
% 4.77/1.91  tff(c_2911, plain, (![A_154, C_155, B_156]: (k4_subset_1(A_154, C_155, B_156)=k4_subset_1(A_154, B_156, C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(A_154)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.77/1.91  tff(c_2977, plain, (![B_157]: (k4_subset_1('#skF_3', B_157, '#skF_4')=k4_subset_1('#skF_3', '#skF_4', B_157) | ~m1_subset_1(B_157, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_2911])).
% 4.77/1.91  tff(c_4696, plain, (![B_190]: (k4_subset_1('#skF_3', k3_subset_1('#skF_3', B_190), '#skF_4')=k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_2977])).
% 4.77/1.91  tff(c_4711, plain, (k4_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_4696])).
% 4.77/1.91  tff(c_4716, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4279, c_4711])).
% 4.77/1.91  tff(c_4718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_4716])).
% 4.77/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.91  
% 4.77/1.91  Inference rules
% 4.77/1.91  ----------------------
% 4.77/1.91  #Ref     : 0
% 4.77/1.91  #Sup     : 1157
% 4.77/1.91  #Fact    : 0
% 4.77/1.91  #Define  : 0
% 4.77/1.91  #Split   : 0
% 4.77/1.91  #Chain   : 0
% 4.77/1.91  #Close   : 0
% 4.77/1.91  
% 4.77/1.91  Ordering : KBO
% 4.77/1.91  
% 4.77/1.91  Simplification rules
% 4.77/1.91  ----------------------
% 4.77/1.91  #Subsume      : 19
% 4.77/1.91  #Demod        : 965
% 4.77/1.91  #Tautology    : 770
% 4.77/1.91  #SimpNegUnit  : 3
% 4.77/1.91  #BackRed      : 11
% 4.77/1.91  
% 4.77/1.91  #Partial instantiations: 0
% 4.77/1.91  #Strategies tried      : 1
% 4.77/1.91  
% 4.77/1.91  Timing (in seconds)
% 4.77/1.91  ----------------------
% 4.77/1.92  Preprocessing        : 0.34
% 4.77/1.92  Parsing              : 0.18
% 4.77/1.92  CNF conversion       : 0.02
% 4.77/1.92  Main loop            : 0.82
% 4.77/1.92  Inferencing          : 0.27
% 4.77/1.92  Reduction            : 0.35
% 4.77/1.92  Demodulation         : 0.28
% 4.77/1.92  BG Simplification    : 0.03
% 4.77/1.92  Subsumption          : 0.11
% 4.77/1.92  Abstraction          : 0.04
% 4.77/1.92  MUC search           : 0.00
% 4.77/1.92  Cooper               : 0.00
% 4.77/1.92  Total                : 1.19
% 4.77/1.92  Index Insertion      : 0.00
% 4.77/1.92  Index Deletion       : 0.00
% 4.77/1.92  Index Matching       : 0.00
% 4.77/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
