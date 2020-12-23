%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 12.08s
% Output     : CNFRefutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 174 expanded)
%              Number of leaves         :   47 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 222 expanded)
%              Number of equality atoms :   65 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_100,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_70,plain,(
    ! [A_59] : k2_subset_1(A_59) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) != k2_subset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80])).

tff(c_28,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_333,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,B_112) = k3_subset_1(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_346,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_333])).

tff(c_76,plain,(
    ! [A_64] : ~ v1_xboole_0(k1_zfmisc_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_189,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | ~ m1_subset_1(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [C_54,A_50] :
      ( r1_tarski(C_54,A_50)
      | ~ r2_hidden(C_54,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_197,plain,(
    ! [B_91,A_50] :
      ( r1_tarski(B_91,A_50)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_50))
      | v1_xboole_0(k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_189,c_48])).

tff(c_202,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_197])).

tff(c_211,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_202])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_211,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_220,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_296,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(B_110,A_109)) = k4_xboole_0(A_109,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_313,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_296])).

tff(c_347,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_313])).

tff(c_358,plain,(
    ! [A_113,B_114,C_115] : k5_xboole_0(k5_xboole_0(A_113,B_114),C_115) = k5_xboole_0(A_113,k5_xboole_0(B_114,C_115)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_380,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k5_xboole_0(B_114,k5_xboole_0(A_113,B_114))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_32])).

tff(c_728,plain,(
    ! [A_123,C_124] : k5_xboole_0(A_123,k5_xboole_0(A_123,C_124)) = k5_xboole_0(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_358])).

tff(c_824,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,A_20) = k5_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_728])).

tff(c_848,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_824])).

tff(c_410,plain,(
    ! [A_20,C_115] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_115)) = k5_xboole_0(k1_xboole_0,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_358])).

tff(c_936,plain,(
    ! [A_128,C_129] : k5_xboole_0(A_128,k5_xboole_0(A_128,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_410])).

tff(c_980,plain,(
    ! [B_114,A_113] : k5_xboole_0(B_114,k5_xboole_0(A_113,B_114)) = k5_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_936])).

tff(c_1070,plain,(
    ! [B_133,A_134] : k5_xboole_0(B_133,k5_xboole_0(A_134,B_133)) = A_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_980])).

tff(c_1117,plain,(
    k5_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_1070])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3648,plain,(
    ! [A_230,B_231,C_232] :
      ( ~ r2_hidden('#skF_1'(A_230,B_231,C_232),B_231)
      | r2_hidden('#skF_2'(A_230,B_231,C_232),C_232)
      | k4_xboole_0(A_230,B_231) = C_232 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3664,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_3648])).

tff(c_4539,plain,(
    ! [A_275,C_276] :
      ( r2_hidden('#skF_2'(A_275,A_275,C_276),C_276)
      | k4_xboole_0(A_275,A_275) = C_276 ) ),
    inference(resolution,[status(thm)],[c_20,c_3648])).

tff(c_1812,plain,(
    ! [A_151,B_152,C_153] : k5_xboole_0(k3_xboole_0(A_151,B_152),k3_xboole_0(C_153,B_152)) = k3_xboole_0(k5_xboole_0(A_151,C_153),B_152) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1847,plain,(
    ! [C_153,B_152] : k3_xboole_0(k5_xboole_0(C_153,C_153),B_152) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_32])).

tff(c_1892,plain,(
    ! [B_154] : k3_xboole_0(k1_xboole_0,B_154) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1847])).

tff(c_232,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_1906,plain,(
    ! [B_154] : k5_xboole_0(B_154,k1_xboole_0) = k4_xboole_0(B_154,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_232])).

tff(c_2038,plain,(
    ! [B_160] : k4_xboole_0(B_160,k1_xboole_0) = B_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1906])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2051,plain,(
    ! [D_8,B_160] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_6])).

tff(c_12257,plain,(
    ! [A_375,B_376] :
      ( ~ r2_hidden('#skF_2'(A_375,A_375,k1_xboole_0),B_376)
      | k4_xboole_0(A_375,A_375) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4539,c_2051])).

tff(c_12292,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3664,c_12257])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1860,plain,(
    ! [A_151,B_10] : k3_xboole_0(k5_xboole_0(A_151,k3_xboole_0(A_151,B_10)),B_10) = k4_xboole_0(k3_xboole_0(A_151,B_10),B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1812])).

tff(c_4587,plain,(
    ! [A_278,B_279] : k4_xboole_0(k3_xboole_0(A_278,B_279),B_279) = k3_xboole_0(B_279,k4_xboole_0(A_278,B_279)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22,c_1860])).

tff(c_4704,plain,(
    ! [A_283,B_284] : k4_xboole_0(k3_xboole_0(A_283,B_284),A_283) = k3_xboole_0(A_283,k4_xboole_0(B_284,A_283)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4587])).

tff(c_4786,plain,(
    k3_xboole_0('#skF_6',k4_xboole_0('#skF_5','#skF_6')) = k4_xboole_0('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_4704])).

tff(c_4806,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k4_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_4786])).

tff(c_12363,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12292,c_4806])).

tff(c_34,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_13053,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')),k1_xboole_0) = k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12363,c_34])).

tff(c_13079,plain,(
    k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1117,c_13053])).

tff(c_74,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k3_subset_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2625,plain,(
    ! [A_190,B_191,C_192] :
      ( k4_subset_1(A_190,B_191,C_192) = k2_xboole_0(B_191,C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_23287,plain,(
    ! [A_478,B_479,B_480] :
      ( k4_subset_1(A_478,B_479,k3_subset_1(A_478,B_480)) = k2_xboole_0(B_479,k3_subset_1(A_478,B_480))
      | ~ m1_subset_1(B_479,k1_zfmisc_1(A_478))
      | ~ m1_subset_1(B_480,k1_zfmisc_1(A_478)) ) ),
    inference(resolution,[status(thm)],[c_74,c_2625])).

tff(c_23322,plain,(
    ! [B_481] :
      ( k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5',B_481)) = k2_xboole_0('#skF_6',k3_subset_1('#skF_5',B_481))
      | ~ m1_subset_1(B_481,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_82,c_23287])).

tff(c_23349,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) = k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_82,c_23322])).

tff(c_23363,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13079,c_23349])).

tff(c_23365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_23363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.08/5.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.08/5.32  
% 12.08/5.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.08/5.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 12.08/5.32  
% 12.08/5.32  %Foreground sorts:
% 12.08/5.32  
% 12.08/5.32  
% 12.08/5.32  %Background operators:
% 12.08/5.32  
% 12.08/5.32  
% 12.08/5.32  %Foreground operators:
% 12.08/5.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.08/5.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.08/5.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.08/5.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.08/5.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.08/5.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.08/5.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.08/5.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.08/5.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.08/5.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.08/5.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.08/5.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.08/5.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.08/5.32  tff('#skF_5', type, '#skF_5': $i).
% 12.08/5.32  tff('#skF_6', type, '#skF_6': $i).
% 12.08/5.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.08/5.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.08/5.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.08/5.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.08/5.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.08/5.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.08/5.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.08/5.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.08/5.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.08/5.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.08/5.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.08/5.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.08/5.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.08/5.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.08/5.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.08/5.32  
% 12.08/5.33  tff(f_89, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.08/5.33  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 12.08/5.33  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.08/5.33  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.08/5.33  tff(f_100, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.08/5.33  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.08/5.33  tff(f_72, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.08/5.34  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.08/5.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.08/5.34  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.08/5.34  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.08/5.34  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.08/5.34  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.08/5.34  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 12.08/5.34  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.08/5.34  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.08/5.34  tff(f_106, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.08/5.34  tff(c_70, plain, (![A_59]: (k2_subset_1(A_59)=A_59)), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.08/5.34  tff(c_80, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))!=k2_subset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.08/5.34  tff(c_83, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80])).
% 12.08/5.34  tff(c_28, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.08/5.34  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.08/5.34  tff(c_333, plain, (![A_111, B_112]: (k4_xboole_0(A_111, B_112)=k3_subset_1(A_111, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.08/5.34  tff(c_346, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_82, c_333])).
% 12.08/5.34  tff(c_76, plain, (![A_64]: (~v1_xboole_0(k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.08/5.34  tff(c_189, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | ~m1_subset_1(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.08/5.34  tff(c_48, plain, (![C_54, A_50]: (r1_tarski(C_54, A_50) | ~r2_hidden(C_54, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.08/5.34  tff(c_197, plain, (![B_91, A_50]: (r1_tarski(B_91, A_50) | ~m1_subset_1(B_91, k1_zfmisc_1(A_50)) | v1_xboole_0(k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_189, c_48])).
% 12.08/5.34  tff(c_202, plain, (![B_93, A_94]: (r1_tarski(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)))), inference(negUnitSimplification, [status(thm)], [c_76, c_197])).
% 12.08/5.34  tff(c_211, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_202])).
% 12.08/5.34  tff(c_26, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.08/5.34  tff(c_215, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_211, c_26])).
% 12.08/5.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.08/5.34  tff(c_220, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.08/5.34  tff(c_296, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(B_110, A_109))=k4_xboole_0(A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_2, c_220])).
% 12.08/5.34  tff(c_313, plain, (k5_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_215, c_296])).
% 12.08/5.34  tff(c_347, plain, (k5_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_313])).
% 12.08/5.34  tff(c_358, plain, (![A_113, B_114, C_115]: (k5_xboole_0(k5_xboole_0(A_113, B_114), C_115)=k5_xboole_0(A_113, k5_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.08/5.34  tff(c_32, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.08/5.34  tff(c_380, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k5_xboole_0(B_114, k5_xboole_0(A_113, B_114)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_358, c_32])).
% 12.08/5.34  tff(c_728, plain, (![A_123, C_124]: (k5_xboole_0(A_123, k5_xboole_0(A_123, C_124))=k5_xboole_0(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_32, c_358])).
% 12.08/5.34  tff(c_824, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, A_20)=k5_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_728])).
% 12.08/5.34  tff(c_848, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_824])).
% 12.08/5.34  tff(c_410, plain, (![A_20, C_115]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_115))=k5_xboole_0(k1_xboole_0, C_115))), inference(superposition, [status(thm), theory('equality')], [c_32, c_358])).
% 12.08/5.34  tff(c_936, plain, (![A_128, C_129]: (k5_xboole_0(A_128, k5_xboole_0(A_128, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_848, c_410])).
% 12.08/5.34  tff(c_980, plain, (![B_114, A_113]: (k5_xboole_0(B_114, k5_xboole_0(A_113, B_114))=k5_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_380, c_936])).
% 12.08/5.34  tff(c_1070, plain, (![B_133, A_134]: (k5_xboole_0(B_133, k5_xboole_0(A_134, B_133))=A_134)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_980])).
% 12.08/5.34  tff(c_1117, plain, (k5_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_347, c_1070])).
% 12.08/5.34  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.08/5.34  tff(c_3648, plain, (![A_230, B_231, C_232]: (~r2_hidden('#skF_1'(A_230, B_231, C_232), B_231) | r2_hidden('#skF_2'(A_230, B_231, C_232), C_232) | k4_xboole_0(A_230, B_231)=C_232)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.08/5.34  tff(c_3664, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_3648])).
% 12.08/5.34  tff(c_4539, plain, (![A_275, C_276]: (r2_hidden('#skF_2'(A_275, A_275, C_276), C_276) | k4_xboole_0(A_275, A_275)=C_276)), inference(resolution, [status(thm)], [c_20, c_3648])).
% 12.08/5.34  tff(c_1812, plain, (![A_151, B_152, C_153]: (k5_xboole_0(k3_xboole_0(A_151, B_152), k3_xboole_0(C_153, B_152))=k3_xboole_0(k5_xboole_0(A_151, C_153), B_152))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.08/5.34  tff(c_1847, plain, (![C_153, B_152]: (k3_xboole_0(k5_xboole_0(C_153, C_153), B_152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1812, c_32])).
% 12.08/5.34  tff(c_1892, plain, (![B_154]: (k3_xboole_0(k1_xboole_0, B_154)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1847])).
% 12.08/5.34  tff(c_232, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_220])).
% 12.08/5.34  tff(c_1906, plain, (![B_154]: (k5_xboole_0(B_154, k1_xboole_0)=k4_xboole_0(B_154, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1892, c_232])).
% 12.08/5.34  tff(c_2038, plain, (![B_160]: (k4_xboole_0(B_160, k1_xboole_0)=B_160)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1906])).
% 12.08/5.34  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.08/5.34  tff(c_2051, plain, (![D_8, B_160]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, B_160))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_6])).
% 12.08/5.34  tff(c_12257, plain, (![A_375, B_376]: (~r2_hidden('#skF_2'(A_375, A_375, k1_xboole_0), B_376) | k4_xboole_0(A_375, A_375)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4539, c_2051])).
% 12.08/5.34  tff(c_12292, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3664, c_12257])).
% 12.08/5.34  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.08/5.34  tff(c_1860, plain, (![A_151, B_10]: (k3_xboole_0(k5_xboole_0(A_151, k3_xboole_0(A_151, B_10)), B_10)=k4_xboole_0(k3_xboole_0(A_151, B_10), B_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1812])).
% 12.08/5.34  tff(c_4587, plain, (![A_278, B_279]: (k4_xboole_0(k3_xboole_0(A_278, B_279), B_279)=k3_xboole_0(B_279, k4_xboole_0(A_278, B_279)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22, c_1860])).
% 12.08/5.34  tff(c_4704, plain, (![A_283, B_284]: (k4_xboole_0(k3_xboole_0(A_283, B_284), A_283)=k3_xboole_0(A_283, k4_xboole_0(B_284, A_283)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4587])).
% 12.08/5.34  tff(c_4786, plain, (k3_xboole_0('#skF_6', k4_xboole_0('#skF_5', '#skF_6'))=k4_xboole_0('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_215, c_4704])).
% 12.08/5.34  tff(c_4806, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k4_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_4786])).
% 12.08/5.34  tff(c_12363, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12292, c_4806])).
% 12.08/5.34  tff(c_34, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.08/5.34  tff(c_13053, plain, (k5_xboole_0(k5_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6')), k1_xboole_0)=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12363, c_34])).
% 12.08/5.34  tff(c_13079, plain, (k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1117, c_13053])).
% 12.08/5.34  tff(c_74, plain, (![A_62, B_63]: (m1_subset_1(k3_subset_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.08/5.34  tff(c_2625, plain, (![A_190, B_191, C_192]: (k4_subset_1(A_190, B_191, C_192)=k2_xboole_0(B_191, C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.08/5.34  tff(c_23287, plain, (![A_478, B_479, B_480]: (k4_subset_1(A_478, B_479, k3_subset_1(A_478, B_480))=k2_xboole_0(B_479, k3_subset_1(A_478, B_480)) | ~m1_subset_1(B_479, k1_zfmisc_1(A_478)) | ~m1_subset_1(B_480, k1_zfmisc_1(A_478)))), inference(resolution, [status(thm)], [c_74, c_2625])).
% 12.08/5.34  tff(c_23322, plain, (![B_481]: (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', B_481))=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', B_481)) | ~m1_subset_1(B_481, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_82, c_23287])).
% 12.08/5.34  tff(c_23349, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_23322])).
% 12.08/5.34  tff(c_23363, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13079, c_23349])).
% 12.08/5.34  tff(c_23365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_23363])).
% 12.08/5.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.08/5.34  
% 12.08/5.34  Inference rules
% 12.08/5.34  ----------------------
% 12.08/5.34  #Ref     : 0
% 12.08/5.34  #Sup     : 5894
% 12.08/5.34  #Fact    : 0
% 12.08/5.34  #Define  : 0
% 12.08/5.34  #Split   : 9
% 12.08/5.34  #Chain   : 0
% 12.08/5.34  #Close   : 0
% 12.08/5.34  
% 12.08/5.34  Ordering : KBO
% 12.08/5.34  
% 12.08/5.34  Simplification rules
% 12.08/5.34  ----------------------
% 12.08/5.34  #Subsume      : 236
% 12.08/5.34  #Demod        : 6823
% 12.08/5.34  #Tautology    : 2261
% 12.08/5.34  #SimpNegUnit  : 44
% 12.08/5.34  #BackRed      : 33
% 12.08/5.34  
% 12.08/5.34  #Partial instantiations: 0
% 12.08/5.34  #Strategies tried      : 1
% 12.08/5.34  
% 12.08/5.34  Timing (in seconds)
% 12.08/5.34  ----------------------
% 12.08/5.34  Preprocessing        : 0.35
% 12.08/5.34  Parsing              : 0.18
% 12.08/5.34  CNF conversion       : 0.02
% 12.08/5.34  Main loop            : 4.18
% 12.08/5.34  Inferencing          : 0.75
% 12.08/5.34  Reduction            : 2.42
% 12.08/5.34  Demodulation         : 2.16
% 12.08/5.34  BG Simplification    : 0.12
% 12.08/5.34  Subsumption          : 0.68
% 12.08/5.34  Abstraction          : 0.18
% 12.08/5.34  MUC search           : 0.00
% 12.08/5.34  Cooper               : 0.00
% 12.08/5.34  Total                : 4.56
% 12.08/5.34  Index Insertion      : 0.00
% 12.08/5.34  Index Deletion       : 0.00
% 12.08/5.34  Index Matching       : 0.00
% 12.08/5.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
