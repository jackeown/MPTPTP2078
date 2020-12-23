%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 29.48s
% Output     : CNFRefutation 29.48s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 157 expanded)
%              Number of leaves         :   46 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 195 expanded)
%              Number of equality atoms :   57 (  95 expanded)
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

tff(f_83,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_94,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_56,plain,(
    ! [A_57] : k2_subset_1(A_57) = A_57 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_489,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(A_108,B_109) = k3_subset_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_502,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_489])).

tff(c_62,plain,(
    ! [A_62] : ~ v1_xboole_0(k1_zfmisc_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_334,plain,(
    ! [B_94,A_95] :
      ( r2_hidden(B_94,A_95)
      | ~ m1_subset_1(B_94,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [C_52,A_48] :
      ( r1_tarski(C_52,A_48)
      | ~ r2_hidden(C_52,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_338,plain,(
    ! [B_94,A_48] :
      ( r1_tarski(B_94,A_48)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_48))
      | v1_xboole_0(k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_334,c_34])).

tff(c_353,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_338])).

tff(c_362,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_353])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_366,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_362,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_388,plain,(
    ! [B_102,A_103] : k5_xboole_0(B_102,k3_xboole_0(A_103,B_102)) = k4_xboole_0(B_102,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_280])).

tff(c_405,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_388])).

tff(c_504,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_405])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [B_73,A_74] : k5_xboole_0(B_73,A_74) = k5_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_14])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_529,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k5_xboole_0(A_110,B_111),C_112) = k5_xboole_0(A_110,k5_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_610,plain,(
    ! [A_18,C_112] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_112)) = k5_xboole_0(k1_xboole_0,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_529])).

tff(c_624,plain,(
    ! [A_113,C_114] : k5_xboole_0(A_113,k5_xboole_0(A_113,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_610])).

tff(c_698,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k5_xboole_0(B_116,A_115)) = B_116 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_624])).

tff(c_748,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_698])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_370,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_8])).

tff(c_373,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_370])).

tff(c_459,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_4])).

tff(c_503,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_459])).

tff(c_300,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_280])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1547,plain,(
    ! [A_134,B_135,C_136] : k5_xboole_0(k3_xboole_0(A_134,B_135),k3_xboole_0(C_136,B_135)) = k3_xboole_0(k5_xboole_0(A_134,C_136),B_135) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1620,plain,(
    ! [A_5,C_136] : k5_xboole_0(A_5,k3_xboole_0(C_136,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_136),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1547])).

tff(c_1950,plain,(
    ! [A_151,C_152] : k3_xboole_0(A_151,k5_xboole_0(A_151,C_152)) = k4_xboole_0(A_151,C_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_2,c_1620])).

tff(c_2024,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_1950])).

tff(c_2059,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_2024])).

tff(c_20,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2143,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2059,c_20])).

tff(c_2154,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_748,c_2143])).

tff(c_60,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k3_subset_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4524,plain,(
    ! [A_200,B_201,C_202] :
      ( k4_subset_1(A_200,B_201,C_202) = k2_xboole_0(B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(A_200))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72344,plain,(
    ! [A_499,B_500,B_501] :
      ( k4_subset_1(A_499,B_500,k3_subset_1(A_499,B_501)) = k2_xboole_0(B_500,k3_subset_1(A_499,B_501))
      | ~ m1_subset_1(B_500,k1_zfmisc_1(A_499))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_499)) ) ),
    inference(resolution,[status(thm)],[c_60,c_4524])).

tff(c_75798,plain,(
    ! [B_508] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_508)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_508))
      | ~ m1_subset_1(B_508,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_68,c_72344])).

tff(c_75821,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_75798])).

tff(c_75833,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_75821])).

tff(c_75835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_75833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.48/21.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/21.35  
% 29.48/21.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/21.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 29.48/21.35  
% 29.48/21.35  %Foreground sorts:
% 29.48/21.35  
% 29.48/21.35  
% 29.48/21.35  %Background operators:
% 29.48/21.35  
% 29.48/21.35  
% 29.48/21.35  %Foreground operators:
% 29.48/21.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.48/21.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.48/21.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.48/21.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.48/21.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 29.48/21.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.48/21.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.48/21.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 29.48/21.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.48/21.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 29.48/21.35  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 29.48/21.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.48/21.35  tff('#skF_3', type, '#skF_3': $i).
% 29.48/21.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 29.48/21.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.48/21.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 29.48/21.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.48/21.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 29.48/21.35  tff('#skF_4', type, '#skF_4': $i).
% 29.48/21.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.48/21.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.48/21.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.48/21.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.48/21.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 29.48/21.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.48/21.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 29.48/21.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 29.48/21.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.48/21.35  
% 29.48/21.37  tff(f_83, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 29.48/21.37  tff(f_105, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 29.48/21.37  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 29.48/21.37  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 29.48/21.37  tff(f_94, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 29.48/21.37  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 29.48/21.37  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 29.48/21.37  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 29.48/21.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.48/21.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 29.48/21.37  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 29.48/21.37  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 29.48/21.37  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 29.48/21.37  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 29.48/21.37  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 29.48/21.37  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 29.48/21.37  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 29.48/21.37  tff(f_100, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 29.48/21.37  tff(c_56, plain, (![A_57]: (k2_subset_1(A_57)=A_57)), inference(cnfTransformation, [status(thm)], [f_83])).
% 29.48/21.37  tff(c_66, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 29.48/21.37  tff(c_69, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 29.48/21.37  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.48/21.37  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 29.48/21.37  tff(c_489, plain, (![A_108, B_109]: (k4_xboole_0(A_108, B_109)=k3_subset_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 29.48/21.37  tff(c_502, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_489])).
% 29.48/21.37  tff(c_62, plain, (![A_62]: (~v1_xboole_0(k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 29.48/21.37  tff(c_334, plain, (![B_94, A_95]: (r2_hidden(B_94, A_95) | ~m1_subset_1(B_94, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_81])).
% 29.48/21.37  tff(c_34, plain, (![C_52, A_48]: (r1_tarski(C_52, A_48) | ~r2_hidden(C_52, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 29.48/21.37  tff(c_338, plain, (![B_94, A_48]: (r1_tarski(B_94, A_48) | ~m1_subset_1(B_94, k1_zfmisc_1(A_48)) | v1_xboole_0(k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_334, c_34])).
% 29.48/21.37  tff(c_353, plain, (![B_98, A_99]: (r1_tarski(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)))), inference(negUnitSimplification, [status(thm)], [c_62, c_338])).
% 29.48/21.37  tff(c_362, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_353])).
% 29.48/21.37  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.48/21.37  tff(c_366, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_362, c_12])).
% 29.48/21.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.48/21.37  tff(c_280, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.48/21.37  tff(c_388, plain, (![B_102, A_103]: (k5_xboole_0(B_102, k3_xboole_0(A_103, B_102))=k4_xboole_0(B_102, A_103))), inference(superposition, [status(thm), theory('equality')], [c_2, c_280])).
% 29.48/21.37  tff(c_405, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_366, c_388])).
% 29.48/21.37  tff(c_504, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_405])).
% 29.48/21.37  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.48/21.37  tff(c_148, plain, (![B_73, A_74]: (k5_xboole_0(B_73, A_74)=k5_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.48/21.37  tff(c_164, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_148, c_14])).
% 29.48/21.37  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.48/21.37  tff(c_529, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k5_xboole_0(A_110, B_111), C_112)=k5_xboole_0(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.48/21.37  tff(c_610, plain, (![A_18, C_112]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_112))=k5_xboole_0(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_18, c_529])).
% 29.48/21.37  tff(c_624, plain, (![A_113, C_114]: (k5_xboole_0(A_113, k5_xboole_0(A_113, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_610])).
% 29.48/21.37  tff(c_698, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k5_xboole_0(B_116, A_115))=B_116)), inference(superposition, [status(thm), theory('equality')], [c_4, c_624])).
% 29.48/21.37  tff(c_748, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_504, c_698])).
% 29.48/21.37  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.48/21.37  tff(c_370, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_366, c_8])).
% 29.48/21.37  tff(c_373, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_370])).
% 29.48/21.37  tff(c_459, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_405, c_4])).
% 29.48/21.37  tff(c_503, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_459])).
% 29.48/21.37  tff(c_300, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_280])).
% 29.48/21.37  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.48/21.37  tff(c_1547, plain, (![A_134, B_135, C_136]: (k5_xboole_0(k3_xboole_0(A_134, B_135), k3_xboole_0(C_136, B_135))=k3_xboole_0(k5_xboole_0(A_134, C_136), B_135))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.48/21.37  tff(c_1620, plain, (![A_5, C_136]: (k5_xboole_0(A_5, k3_xboole_0(C_136, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_136), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1547])).
% 29.48/21.37  tff(c_1950, plain, (![A_151, C_152]: (k3_xboole_0(A_151, k5_xboole_0(A_151, C_152))=k4_xboole_0(A_151, C_152))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_2, c_1620])).
% 29.48/21.37  tff(c_2024, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_503, c_1950])).
% 29.48/21.37  tff(c_2059, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_373, c_2024])).
% 29.48/21.37  tff(c_20, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.48/21.37  tff(c_2143, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2059, c_20])).
% 29.48/21.37  tff(c_2154, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_748, c_2143])).
% 29.48/21.37  tff(c_60, plain, (![A_60, B_61]: (m1_subset_1(k3_subset_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.48/21.37  tff(c_4524, plain, (![A_200, B_201, C_202]: (k4_subset_1(A_200, B_201, C_202)=k2_xboole_0(B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(A_200)) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 29.48/21.37  tff(c_72344, plain, (![A_499, B_500, B_501]: (k4_subset_1(A_499, B_500, k3_subset_1(A_499, B_501))=k2_xboole_0(B_500, k3_subset_1(A_499, B_501)) | ~m1_subset_1(B_500, k1_zfmisc_1(A_499)) | ~m1_subset_1(B_501, k1_zfmisc_1(A_499)))), inference(resolution, [status(thm)], [c_60, c_4524])).
% 29.48/21.37  tff(c_75798, plain, (![B_508]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_508))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_508)) | ~m1_subset_1(B_508, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_68, c_72344])).
% 29.48/21.37  tff(c_75821, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_75798])).
% 29.48/21.37  tff(c_75833, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_75821])).
% 29.48/21.37  tff(c_75835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_75833])).
% 29.48/21.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/21.37  
% 29.48/21.37  Inference rules
% 29.48/21.37  ----------------------
% 29.48/21.37  #Ref     : 0
% 29.48/21.37  #Sup     : 19924
% 29.48/21.37  #Fact    : 0
% 29.48/21.37  #Define  : 0
% 29.48/21.37  #Split   : 0
% 29.48/21.37  #Chain   : 0
% 29.48/21.37  #Close   : 0
% 29.48/21.37  
% 29.48/21.37  Ordering : KBO
% 29.48/21.37  
% 29.48/21.37  Simplification rules
% 29.48/21.37  ----------------------
% 29.48/21.37  #Subsume      : 1047
% 29.48/21.37  #Demod        : 28735
% 29.48/21.37  #Tautology    : 6268
% 29.48/21.37  #SimpNegUnit  : 22
% 29.48/21.37  #BackRed      : 8
% 29.48/21.37  
% 29.48/21.37  #Partial instantiations: 0
% 29.48/21.37  #Strategies tried      : 1
% 29.48/21.37  
% 29.48/21.37  Timing (in seconds)
% 29.48/21.37  ----------------------
% 29.48/21.37  Preprocessing        : 0.35
% 29.48/21.37  Parsing              : 0.18
% 29.48/21.37  CNF conversion       : 0.02
% 29.48/21.37  Main loop            : 20.24
% 29.48/21.37  Inferencing          : 1.72
% 29.48/21.37  Reduction            : 15.27
% 29.48/21.37  Demodulation         : 14.56
% 29.48/21.37  BG Simplification    : 0.33
% 29.48/21.37  Subsumption          : 2.49
% 29.48/21.37  Abstraction          : 0.55
% 29.48/21.37  MUC search           : 0.00
% 29.48/21.37  Cooper               : 0.00
% 29.48/21.38  Total                : 20.63
% 29.48/21.38  Index Insertion      : 0.00
% 29.48/21.38  Index Deletion       : 0.00
% 29.48/21.38  Index Matching       : 0.00
% 29.48/21.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
