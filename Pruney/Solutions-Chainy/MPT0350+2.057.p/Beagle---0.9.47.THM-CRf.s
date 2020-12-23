%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 11.94s
% Output     : CNFRefutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 327 expanded)
%              Number of leaves         :   44 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 462 expanded)
%              Number of equality atoms :   69 ( 212 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_81,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

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

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
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

tff(c_54,plain,(
    ! [A_57] : k2_subset_1(A_57) = A_57 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_304,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_316,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_508,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_525,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k5_xboole_0(B_112,k3_xboole_0(A_111,B_112))) = k2_xboole_0(A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_18])).

tff(c_609,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k4_xboole_0(B_112,A_111)) = k2_xboole_0(A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_525])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_929,plain,(
    ! [B_127,A_128,C_129] : k5_xboole_0(k5_xboole_0(B_127,A_128),C_129) = k5_xboole_0(A_128,k5_xboole_0(B_127,C_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_508])).

tff(c_959,plain,(
    ! [A_128,B_127] : k5_xboole_0(A_128,k5_xboole_0(B_127,k3_xboole_0(B_127,A_128))) = k2_xboole_0(B_127,A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_18])).

tff(c_1066,plain,(
    ! [B_127,A_128] : k2_xboole_0(B_127,A_128) = k2_xboole_0(A_128,B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_8,c_959])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [A_62] : ~ v1_xboole_0(k1_zfmisc_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_254,plain,(
    ! [B_94,A_95] :
      ( r2_hidden(B_94,A_95)
      | ~ m1_subset_1(B_94,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [C_52,A_48] :
      ( r1_tarski(C_52,A_48)
      | ~ r2_hidden(C_52,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_261,plain,(
    ! [B_94,A_48] :
      ( r1_tarski(B_94,A_48)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_48))
      | v1_xboole_0(k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_254,c_32])).

tff(c_271,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_261])).

tff(c_284,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_271])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_288,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_284,c_14])).

tff(c_153,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = A_73 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_292,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_162])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_322,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_304])).

tff(c_313,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_304])).

tff(c_334,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_313])).

tff(c_613,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(A_114,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_525])).

tff(c_649,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_613])).

tff(c_656,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_649])).

tff(c_339,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(B_104,A_103)) = k4_xboole_0(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_356,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_339])).

tff(c_406,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_430,plain,(
    k5_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_406])).

tff(c_469,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_288,c_4,c_2,c_430])).

tff(c_376,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_4])).

tff(c_442,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_406])).

tff(c_473,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_376,c_442])).

tff(c_495,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_473])).

tff(c_657,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k3_subset_1(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_670,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_657])).

tff(c_677,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_609])).

tff(c_680,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_677])).

tff(c_673,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_356])).

tff(c_1884,plain,(
    ! [A_146,B_147,C_148] : k5_xboole_0(k3_xboole_0(A_146,B_147),k3_xboole_0(C_148,B_147)) = k3_xboole_0(k5_xboole_0(A_146,C_148),B_147) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1963,plain,(
    ! [A_5,C_148] : k5_xboole_0(A_5,k3_xboole_0(C_148,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_148),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1884])).

tff(c_1977,plain,(
    ! [A_149,C_150] : k3_xboole_0(A_149,k5_xboole_0(A_149,C_150)) = k4_xboole_0(A_149,C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_2,c_1963])).

tff(c_2244,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k5_xboole_0(B_156,A_155)) = k4_xboole_0(A_155,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1977])).

tff(c_2333,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_2244])).

tff(c_2376,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_2333])).

tff(c_445,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_406])).

tff(c_2533,plain,(
    k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4'),k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2376,c_445])).

tff(c_2562,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_656,c_4,c_680,c_4,c_4,c_2533])).

tff(c_58,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k3_subset_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3630,plain,(
    ! [A_189,B_190,C_191] :
      ( k4_subset_1(A_189,B_190,C_191) = k2_xboole_0(B_190,C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(A_189))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_23540,plain,(
    ! [A_367,B_368,B_369] :
      ( k4_subset_1(A_367,B_368,k3_subset_1(A_367,B_369)) = k2_xboole_0(B_368,k3_subset_1(A_367,B_369))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(A_367))
      | ~ m1_subset_1(B_369,k1_zfmisc_1(A_367)) ) ),
    inference(resolution,[status(thm)],[c_58,c_3630])).

tff(c_23563,plain,(
    ! [B_370] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_370)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_370))
      | ~ m1_subset_1(B_370,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_66,c_23540])).

tff(c_23582,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_23563])).

tff(c_23590,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_23582])).

tff(c_23592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_23590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.94/5.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/5.63  
% 11.94/5.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.98/5.64  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.98/5.64  
% 11.98/5.64  %Foreground sorts:
% 11.98/5.64  
% 11.98/5.64  
% 11.98/5.64  %Background operators:
% 11.98/5.64  
% 11.98/5.64  
% 11.98/5.64  %Foreground operators:
% 11.98/5.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.98/5.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.98/5.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.98/5.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.98/5.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.98/5.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.98/5.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.98/5.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.98/5.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.98/5.64  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.98/5.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.98/5.64  tff('#skF_3', type, '#skF_3': $i).
% 11.98/5.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.98/5.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.98/5.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.98/5.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.98/5.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.98/5.64  tff('#skF_4', type, '#skF_4': $i).
% 11.98/5.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.98/5.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.98/5.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.98/5.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.98/5.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.98/5.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.98/5.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.98/5.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.98/5.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.98/5.64  
% 11.98/5.65  tff(f_81, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.98/5.65  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 11.98/5.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.98/5.65  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.98/5.65  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.98/5.65  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.98/5.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.98/5.65  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.98/5.65  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.98/5.65  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.98/5.65  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.98/5.65  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.98/5.65  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.98/5.65  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.98/5.65  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 11.98/5.65  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.98/5.65  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.98/5.65  tff(c_54, plain, (![A_57]: (k2_subset_1(A_57)=A_57)), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.98/5.65  tff(c_64, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.98/5.65  tff(c_67, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 11.98/5.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.98/5.65  tff(c_304, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.98/5.65  tff(c_316, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 11.98/5.65  tff(c_508, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.98/5.65  tff(c_18, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.98/5.65  tff(c_525, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k5_xboole_0(B_112, k3_xboole_0(A_111, B_112)))=k2_xboole_0(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_508, c_18])).
% 11.98/5.65  tff(c_609, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k4_xboole_0(B_112, A_111))=k2_xboole_0(A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_525])).
% 11.98/5.65  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.98/5.65  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.98/5.65  tff(c_929, plain, (![B_127, A_128, C_129]: (k5_xboole_0(k5_xboole_0(B_127, A_128), C_129)=k5_xboole_0(A_128, k5_xboole_0(B_127, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_508])).
% 11.98/5.65  tff(c_959, plain, (![A_128, B_127]: (k5_xboole_0(A_128, k5_xboole_0(B_127, k3_xboole_0(B_127, A_128)))=k2_xboole_0(B_127, A_128))), inference(superposition, [status(thm), theory('equality')], [c_929, c_18])).
% 11.98/5.65  tff(c_1066, plain, (![B_127, A_128]: (k2_xboole_0(B_127, A_128)=k2_xboole_0(A_128, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_8, c_959])).
% 11.98/5.65  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.98/5.65  tff(c_60, plain, (![A_62]: (~v1_xboole_0(k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.98/5.65  tff(c_254, plain, (![B_94, A_95]: (r2_hidden(B_94, A_95) | ~m1_subset_1(B_94, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.98/5.65  tff(c_32, plain, (![C_52, A_48]: (r1_tarski(C_52, A_48) | ~r2_hidden(C_52, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.98/5.65  tff(c_261, plain, (![B_94, A_48]: (r1_tarski(B_94, A_48) | ~m1_subset_1(B_94, k1_zfmisc_1(A_48)) | v1_xboole_0(k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_254, c_32])).
% 11.98/5.65  tff(c_271, plain, (![B_98, A_99]: (r1_tarski(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)))), inference(negUnitSimplification, [status(thm)], [c_60, c_261])).
% 11.98/5.65  tff(c_284, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_271])).
% 11.98/5.65  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.98/5.65  tff(c_288, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_284, c_14])).
% 11.98/5.65  tff(c_153, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k3_xboole_0(A_73, B_74))=A_73)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.98/5.65  tff(c_162, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 11.98/5.65  tff(c_292, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_288, c_162])).
% 11.98/5.65  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.98/5.65  tff(c_322, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_304])).
% 11.98/5.65  tff(c_313, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_288, c_304])).
% 11.98/5.65  tff(c_334, plain, (k4_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_313])).
% 11.98/5.65  tff(c_613, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_525])).
% 11.98/5.65  tff(c_649, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_334, c_613])).
% 11.98/5.65  tff(c_656, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_649])).
% 11.98/5.65  tff(c_339, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(B_104, A_103))=k4_xboole_0(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 11.98/5.65  tff(c_356, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_288, c_339])).
% 11.98/5.65  tff(c_406, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.98/5.65  tff(c_430, plain, (k5_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_356, c_406])).
% 11.98/5.65  tff(c_469, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_288, c_4, c_2, c_430])).
% 11.98/5.65  tff(c_376, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_356, c_4])).
% 11.98/5.65  tff(c_442, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_288, c_406])).
% 11.98/5.65  tff(c_473, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_376, c_442])).
% 11.98/5.65  tff(c_495, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_473])).
% 11.98/5.65  tff(c_657, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k3_subset_1(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.98/5.65  tff(c_670, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_657])).
% 11.98/5.65  tff(c_677, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_670, c_609])).
% 11.98/5.65  tff(c_680, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_677])).
% 11.98/5.65  tff(c_673, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_356])).
% 11.98/5.65  tff(c_1884, plain, (![A_146, B_147, C_148]: (k5_xboole_0(k3_xboole_0(A_146, B_147), k3_xboole_0(C_148, B_147))=k3_xboole_0(k5_xboole_0(A_146, C_148), B_147))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.98/5.65  tff(c_1963, plain, (![A_5, C_148]: (k5_xboole_0(A_5, k3_xboole_0(C_148, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_148), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1884])).
% 11.98/5.65  tff(c_1977, plain, (![A_149, C_150]: (k3_xboole_0(A_149, k5_xboole_0(A_149, C_150))=k4_xboole_0(A_149, C_150))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_2, c_1963])).
% 11.98/5.65  tff(c_2244, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k5_xboole_0(B_156, A_155))=k4_xboole_0(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1977])).
% 11.98/5.65  tff(c_2333, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_673, c_2244])).
% 11.98/5.65  tff(c_2376, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_2333])).
% 11.98/5.65  tff(c_445, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_406])).
% 11.98/5.65  tff(c_2533, plain, (k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4'), k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2376, c_445])).
% 11.98/5.65  tff(c_2562, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_656, c_4, c_680, c_4, c_4, c_2533])).
% 11.98/5.65  tff(c_58, plain, (![A_60, B_61]: (m1_subset_1(k3_subset_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.98/5.65  tff(c_3630, plain, (![A_189, B_190, C_191]: (k4_subset_1(A_189, B_190, C_191)=k2_xboole_0(B_190, C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(A_189)) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.98/5.65  tff(c_23540, plain, (![A_367, B_368, B_369]: (k4_subset_1(A_367, B_368, k3_subset_1(A_367, B_369))=k2_xboole_0(B_368, k3_subset_1(A_367, B_369)) | ~m1_subset_1(B_368, k1_zfmisc_1(A_367)) | ~m1_subset_1(B_369, k1_zfmisc_1(A_367)))), inference(resolution, [status(thm)], [c_58, c_3630])).
% 11.98/5.65  tff(c_23563, plain, (![B_370]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_370))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_370)) | ~m1_subset_1(B_370, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_23540])).
% 11.98/5.65  tff(c_23582, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_23563])).
% 11.98/5.65  tff(c_23590, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_23582])).
% 11.98/5.65  tff(c_23592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_23590])).
% 11.98/5.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.98/5.65  
% 11.98/5.65  Inference rules
% 11.98/5.65  ----------------------
% 11.98/5.65  #Ref     : 0
% 11.98/5.65  #Sup     : 6100
% 11.98/5.65  #Fact    : 0
% 11.98/5.65  #Define  : 0
% 11.98/5.65  #Split   : 0
% 11.98/5.65  #Chain   : 0
% 11.98/5.65  #Close   : 0
% 11.98/5.65  
% 11.98/5.65  Ordering : KBO
% 11.98/5.65  
% 11.98/5.65  Simplification rules
% 11.98/5.65  ----------------------
% 11.98/5.65  #Subsume      : 167
% 11.98/5.65  #Demod        : 8668
% 11.98/5.65  #Tautology    : 2471
% 11.98/5.65  #SimpNegUnit  : 14
% 11.98/5.65  #BackRed      : 9
% 11.98/5.65  
% 11.98/5.65  #Partial instantiations: 0
% 11.98/5.65  #Strategies tried      : 1
% 11.98/5.65  
% 11.98/5.65  Timing (in seconds)
% 11.98/5.65  ----------------------
% 11.98/5.66  Preprocessing        : 0.33
% 11.98/5.66  Parsing              : 0.17
% 11.98/5.66  CNF conversion       : 0.02
% 11.98/5.66  Main loop            : 4.49
% 11.98/5.66  Inferencing          : 0.69
% 11.98/5.66  Reduction            : 2.88
% 11.98/5.66  Demodulation         : 2.65
% 11.98/5.66  BG Simplification    : 0.12
% 11.98/5.66  Subsumption          : 0.61
% 11.98/5.66  Abstraction          : 0.18
% 11.98/5.66  MUC search           : 0.00
% 11.98/5.66  Cooper               : 0.00
% 11.98/5.66  Total                : 4.86
% 11.98/5.66  Index Insertion      : 0.00
% 11.98/5.66  Index Deletion       : 0.00
% 11.98/5.66  Index Matching       : 0.00
% 11.98/5.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
