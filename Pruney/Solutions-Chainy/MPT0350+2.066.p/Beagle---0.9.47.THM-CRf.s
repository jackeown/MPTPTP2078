%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 23.14s
% Output     : CNFRefutation 23.14s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 349 expanded)
%              Number of leaves         :   51 ( 140 expanded)
%              Depth                    :   17
%              Number of atoms          :  108 ( 450 expanded)
%              Number of equality atoms :   63 ( 247 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_122,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_102,plain,(
    ! [A_69] : k2_subset_1(A_69) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_112,plain,(
    k4_subset_1('#skF_9','#skF_10',k3_subset_1('#skF_9','#skF_10')) != k2_subset_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_115,plain,(
    k4_subset_1('#skF_9','#skF_10',k3_subset_1('#skF_9','#skF_10')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_112])).

tff(c_114,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_108,plain,(
    ! [A_74] : ~ v1_xboole_0(k1_zfmisc_1(A_74)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_505,plain,(
    ! [B_128,A_129] :
      ( r2_hidden(B_128,A_129)
      | ~ m1_subset_1(B_128,A_129)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_80,plain,(
    ! [C_64,A_60] :
      ( r1_tarski(C_64,A_60)
      | ~ r2_hidden(C_64,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_522,plain,(
    ! [B_128,A_60] :
      ( r1_tarski(B_128,A_60)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_60))
      | v1_xboole_0(k1_zfmisc_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_505,c_80])).

tff(c_662,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(B_144,A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_145)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_522])).

tff(c_675,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_114,c_662])).

tff(c_56,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_682,plain,(
    k3_xboole_0('#skF_10','#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_675,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_689,plain,(
    k3_xboole_0('#skF_9','#skF_10') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_2])).

tff(c_847,plain,(
    ! [A_155,B_156] :
      ( k4_xboole_0(A_155,B_156) = k3_subset_1(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_860,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k3_subset_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_114,c_847])).

tff(c_60,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_868,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9','#skF_10')) = k3_xboole_0('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_60])).

tff(c_877,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_9','#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_868])).

tff(c_64,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [A_24] : r1_tarski(k1_xboole_0,A_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_195,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,(
    ! [A_95] : k3_xboole_0(k1_xboole_0,A_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_195])).

tff(c_209,plain,(
    ! [A_95] : k3_xboole_0(A_95,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_2])).

tff(c_363,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k3_xboole_0(A_120,B_121)) = k4_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_372,plain,(
    ! [A_95] : k5_xboole_0(A_95,k1_xboole_0) = k4_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_363])).

tff(c_387,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_372])).

tff(c_416,plain,(
    ! [A_123] : k4_xboole_0(A_123,k1_xboole_0) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_372])).

tff(c_426,plain,(
    ! [A_123] : k4_xboole_0(A_123,A_123) = k3_xboole_0(A_123,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_60])).

tff(c_442,plain,(
    ! [A_123] : k4_xboole_0(A_123,A_123) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_426])).

tff(c_52,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_52,c_195])).

tff(c_375,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_363])).

tff(c_480,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_375])).

tff(c_885,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_9','#skF_10')) = k4_xboole_0('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_60])).

tff(c_894,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_9','#skF_10')) = k3_subset_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_885])).

tff(c_384,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_363])).

tff(c_1020,plain,(
    k5_xboole_0(k3_subset_1('#skF_9','#skF_10'),k3_subset_1('#skF_9','#skF_10')) = k4_xboole_0(k3_subset_1('#skF_9','#skF_10'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_384])).

tff(c_1026,plain,(
    k4_xboole_0(k3_subset_1('#skF_9','#skF_10'),'#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1020])).

tff(c_1659,plain,(
    ! [A_205,B_206,C_207] : k2_xboole_0(k4_xboole_0(A_205,B_206),k3_xboole_0(A_205,C_207)) = k4_xboole_0(A_205,k4_xboole_0(B_206,C_207)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2516,plain,(
    ! [B_224,B_225] : k4_xboole_0(B_224,k4_xboole_0(B_225,B_224)) = k2_xboole_0(k4_xboole_0(B_224,B_225),B_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_1659])).

tff(c_2569,plain,(
    k2_xboole_0(k4_xboole_0('#skF_9',k3_subset_1('#skF_9','#skF_10')),'#skF_9') = k4_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_2516])).

tff(c_2603,plain,(
    k2_xboole_0('#skF_10','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_387,c_2569])).

tff(c_66,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_865,plain,(
    k5_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) = k2_xboole_0('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_66])).

tff(c_2699,plain,(
    k5_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_865])).

tff(c_1704,plain,(
    ! [A_123,C_207] : k4_xboole_0(A_123,k4_xboole_0(A_123,C_207)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_123,C_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_1659])).

tff(c_1982,plain,(
    ! [A_214,C_215] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_214,C_215)) = k3_xboole_0(A_214,C_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1704])).

tff(c_2028,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = k2_xboole_0(k1_xboole_0,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_1982])).

tff(c_2048,plain,(
    ! [B_19] : k2_xboole_0(k1_xboole_0,B_19) = B_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_2028])).

tff(c_2572,plain,(
    k2_xboole_0(k4_xboole_0(k3_subset_1('#skF_9','#skF_10'),'#skF_9'),k3_subset_1('#skF_9','#skF_10')) = k4_xboole_0(k3_subset_1('#skF_9','#skF_10'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_2516])).

tff(c_2604,plain,(
    k4_xboole_0(k3_subset_1('#skF_9','#skF_10'),'#skF_10') = k3_subset_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_1026,c_2572])).

tff(c_2866,plain,(
    k5_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) = k2_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2604,c_66])).

tff(c_2881,plain,(
    k2_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_2866])).

tff(c_106,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k3_subset_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5613,plain,(
    ! [A_292,B_293,C_294] :
      ( k4_subset_1(A_292,B_293,C_294) = k2_xboole_0(B_293,C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(A_292))
      | ~ m1_subset_1(B_293,k1_zfmisc_1(A_292)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_76624,plain,(
    ! [A_868,B_869,B_870] :
      ( k4_subset_1(A_868,B_869,k3_subset_1(A_868,B_870)) = k2_xboole_0(B_869,k3_subset_1(A_868,B_870))
      | ~ m1_subset_1(B_869,k1_zfmisc_1(A_868))
      | ~ m1_subset_1(B_870,k1_zfmisc_1(A_868)) ) ),
    inference(resolution,[status(thm)],[c_106,c_5613])).

tff(c_76708,plain,(
    ! [B_871] :
      ( k4_subset_1('#skF_9','#skF_10',k3_subset_1('#skF_9',B_871)) = k2_xboole_0('#skF_10',k3_subset_1('#skF_9',B_871))
      | ~ m1_subset_1(B_871,k1_zfmisc_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_114,c_76624])).

tff(c_76771,plain,(
    k4_subset_1('#skF_9','#skF_10',k3_subset_1('#skF_9','#skF_10')) = k2_xboole_0('#skF_10',k3_subset_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_114,c_76708])).

tff(c_76811,plain,(
    k4_subset_1('#skF_9','#skF_10',k3_subset_1('#skF_9','#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2881,c_76771])).

tff(c_76813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_76811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.14/13.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/13.98  
% 23.14/13.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/13.99  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5
% 23.14/13.99  
% 23.14/13.99  %Foreground sorts:
% 23.14/13.99  
% 23.14/13.99  
% 23.14/13.99  %Background operators:
% 23.14/13.99  
% 23.14/13.99  
% 23.14/13.99  %Foreground operators:
% 23.14/13.99  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 23.14/13.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.14/13.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.14/13.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.14/13.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.14/13.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.14/13.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.14/13.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 23.14/13.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.14/13.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.14/13.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.14/13.99  tff('#skF_10', type, '#skF_10': $i).
% 23.14/13.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.14/13.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.14/13.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.14/13.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.14/13.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.14/13.99  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 23.14/13.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.14/13.99  tff('#skF_9', type, '#skF_9': $i).
% 23.14/13.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.14/13.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.14/13.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.14/13.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.14/13.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.14/13.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.14/13.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.14/13.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.14/13.99  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 23.14/13.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.14/13.99  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.14/13.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.14/13.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 23.14/13.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.14/13.99  
% 23.14/14.00  tff(f_111, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 23.14/14.00  tff(f_133, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 23.14/14.00  tff(f_122, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 23.14/14.00  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 23.14/14.00  tff(f_94, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 23.14/14.00  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.14/14.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.14/14.00  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 23.14/14.00  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.14/14.00  tff(f_73, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 23.14/14.00  tff(f_67, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.14/14.00  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 23.14/14.00  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.14/14.00  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 23.14/14.00  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 23.14/14.00  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 23.14/14.00  tff(f_128, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.14/14.00  tff(c_102, plain, (![A_69]: (k2_subset_1(A_69)=A_69)), inference(cnfTransformation, [status(thm)], [f_111])).
% 23.14/14.00  tff(c_112, plain, (k4_subset_1('#skF_9', '#skF_10', k3_subset_1('#skF_9', '#skF_10'))!=k2_subset_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_133])).
% 23.14/14.00  tff(c_115, plain, (k4_subset_1('#skF_9', '#skF_10', k3_subset_1('#skF_9', '#skF_10'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_112])).
% 23.14/14.00  tff(c_114, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 23.14/14.00  tff(c_108, plain, (![A_74]: (~v1_xboole_0(k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.14/14.00  tff(c_505, plain, (![B_128, A_129]: (r2_hidden(B_128, A_129) | ~m1_subset_1(B_128, A_129) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.14/14.00  tff(c_80, plain, (![C_64, A_60]: (r1_tarski(C_64, A_60) | ~r2_hidden(C_64, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 23.14/14.00  tff(c_522, plain, (![B_128, A_60]: (r1_tarski(B_128, A_60) | ~m1_subset_1(B_128, k1_zfmisc_1(A_60)) | v1_xboole_0(k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_505, c_80])).
% 23.14/14.00  tff(c_662, plain, (![B_144, A_145]: (r1_tarski(B_144, A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(A_145)))), inference(negUnitSimplification, [status(thm)], [c_108, c_522])).
% 23.14/14.00  tff(c_675, plain, (r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_114, c_662])).
% 23.14/14.00  tff(c_56, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.14/14.00  tff(c_682, plain, (k3_xboole_0('#skF_10', '#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_675, c_56])).
% 23.14/14.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.14/14.00  tff(c_689, plain, (k3_xboole_0('#skF_9', '#skF_10')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_682, c_2])).
% 23.14/14.00  tff(c_847, plain, (![A_155, B_156]: (k4_xboole_0(A_155, B_156)=k3_subset_1(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 23.14/14.00  tff(c_860, plain, (k4_xboole_0('#skF_9', '#skF_10')=k3_subset_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_114, c_847])).
% 23.14/14.00  tff(c_60, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 23.14/14.00  tff(c_868, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', '#skF_10'))=k3_xboole_0('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_860, c_60])).
% 23.14/14.00  tff(c_877, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_9', '#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_689, c_868])).
% 23.14/14.00  tff(c_64, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.14/14.00  tff(c_58, plain, (![A_24]: (r1_tarski(k1_xboole_0, A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.14/14.00  tff(c_195, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.14/14.00  tff(c_204, plain, (![A_95]: (k3_xboole_0(k1_xboole_0, A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_195])).
% 23.14/14.00  tff(c_209, plain, (![A_95]: (k3_xboole_0(A_95, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_204, c_2])).
% 23.14/14.00  tff(c_363, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k3_xboole_0(A_120, B_121))=k4_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.14/14.00  tff(c_372, plain, (![A_95]: (k5_xboole_0(A_95, k1_xboole_0)=k4_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_209, c_363])).
% 23.14/14.00  tff(c_387, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_372])).
% 23.14/14.00  tff(c_416, plain, (![A_123]: (k4_xboole_0(A_123, k1_xboole_0)=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_372])).
% 23.14/14.00  tff(c_426, plain, (![A_123]: (k4_xboole_0(A_123, A_123)=k3_xboole_0(A_123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_416, c_60])).
% 23.14/14.00  tff(c_442, plain, (![A_123]: (k4_xboole_0(A_123, A_123)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_209, c_426])).
% 23.14/14.00  tff(c_52, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.14/14.00  tff(c_203, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_52, c_195])).
% 23.14/14.00  tff(c_375, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_203, c_363])).
% 23.14/14.00  tff(c_480, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_442, c_375])).
% 23.14/14.00  tff(c_885, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_9', '#skF_10'))=k4_xboole_0('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_877, c_60])).
% 23.14/14.00  tff(c_894, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_9', '#skF_10'))=k3_subset_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_885])).
% 23.14/14.00  tff(c_384, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_363])).
% 23.14/14.00  tff(c_1020, plain, (k5_xboole_0(k3_subset_1('#skF_9', '#skF_10'), k3_subset_1('#skF_9', '#skF_10'))=k4_xboole_0(k3_subset_1('#skF_9', '#skF_10'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_894, c_384])).
% 23.14/14.00  tff(c_1026, plain, (k4_xboole_0(k3_subset_1('#skF_9', '#skF_10'), '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1020])).
% 23.14/14.00  tff(c_1659, plain, (![A_205, B_206, C_207]: (k2_xboole_0(k4_xboole_0(A_205, B_206), k3_xboole_0(A_205, C_207))=k4_xboole_0(A_205, k4_xboole_0(B_206, C_207)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.14/14.00  tff(c_2516, plain, (![B_224, B_225]: (k4_xboole_0(B_224, k4_xboole_0(B_225, B_224))=k2_xboole_0(k4_xboole_0(B_224, B_225), B_224))), inference(superposition, [status(thm), theory('equality')], [c_203, c_1659])).
% 23.14/14.00  tff(c_2569, plain, (k2_xboole_0(k4_xboole_0('#skF_9', k3_subset_1('#skF_9', '#skF_10')), '#skF_9')=k4_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1026, c_2516])).
% 23.14/14.00  tff(c_2603, plain, (k2_xboole_0('#skF_10', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_877, c_387, c_2569])).
% 23.14/14.00  tff(c_66, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.14/14.00  tff(c_865, plain, (k5_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))=k2_xboole_0('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_860, c_66])).
% 23.14/14.00  tff(c_2699, plain, (k5_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_865])).
% 23.14/14.00  tff(c_1704, plain, (![A_123, C_207]: (k4_xboole_0(A_123, k4_xboole_0(A_123, C_207))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_123, C_207)))), inference(superposition, [status(thm), theory('equality')], [c_442, c_1659])).
% 23.14/14.00  tff(c_1982, plain, (![A_214, C_215]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_214, C_215))=k3_xboole_0(A_214, C_215))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1704])).
% 23.14/14.00  tff(c_2028, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=k2_xboole_0(k1_xboole_0, B_19))), inference(superposition, [status(thm), theory('equality')], [c_203, c_1982])).
% 23.14/14.00  tff(c_2048, plain, (![B_19]: (k2_xboole_0(k1_xboole_0, B_19)=B_19)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_2028])).
% 23.14/14.00  tff(c_2572, plain, (k2_xboole_0(k4_xboole_0(k3_subset_1('#skF_9', '#skF_10'), '#skF_9'), k3_subset_1('#skF_9', '#skF_10'))=k4_xboole_0(k3_subset_1('#skF_9', '#skF_10'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_877, c_2516])).
% 23.14/14.00  tff(c_2604, plain, (k4_xboole_0(k3_subset_1('#skF_9', '#skF_10'), '#skF_10')=k3_subset_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_1026, c_2572])).
% 23.14/14.00  tff(c_2866, plain, (k5_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))=k2_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2604, c_66])).
% 23.14/14.00  tff(c_2881, plain, (k2_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_2866])).
% 23.14/14.00  tff(c_106, plain, (![A_72, B_73]: (m1_subset_1(k3_subset_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 23.14/14.00  tff(c_5613, plain, (![A_292, B_293, C_294]: (k4_subset_1(A_292, B_293, C_294)=k2_xboole_0(B_293, C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(A_292)) | ~m1_subset_1(B_293, k1_zfmisc_1(A_292)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.14/14.00  tff(c_76624, plain, (![A_868, B_869, B_870]: (k4_subset_1(A_868, B_869, k3_subset_1(A_868, B_870))=k2_xboole_0(B_869, k3_subset_1(A_868, B_870)) | ~m1_subset_1(B_869, k1_zfmisc_1(A_868)) | ~m1_subset_1(B_870, k1_zfmisc_1(A_868)))), inference(resolution, [status(thm)], [c_106, c_5613])).
% 23.14/14.00  tff(c_76708, plain, (![B_871]: (k4_subset_1('#skF_9', '#skF_10', k3_subset_1('#skF_9', B_871))=k2_xboole_0('#skF_10', k3_subset_1('#skF_9', B_871)) | ~m1_subset_1(B_871, k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_114, c_76624])).
% 23.14/14.00  tff(c_76771, plain, (k4_subset_1('#skF_9', '#skF_10', k3_subset_1('#skF_9', '#skF_10'))=k2_xboole_0('#skF_10', k3_subset_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_114, c_76708])).
% 23.14/14.00  tff(c_76811, plain, (k4_subset_1('#skF_9', '#skF_10', k3_subset_1('#skF_9', '#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2881, c_76771])).
% 23.14/14.00  tff(c_76813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_76811])).
% 23.14/14.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/14.00  
% 23.14/14.00  Inference rules
% 23.14/14.00  ----------------------
% 23.14/14.00  #Ref     : 0
% 23.14/14.00  #Sup     : 18789
% 23.14/14.00  #Fact    : 6
% 23.14/14.00  #Define  : 0
% 23.14/14.00  #Split   : 11
% 23.14/14.00  #Chain   : 0
% 23.14/14.00  #Close   : 0
% 23.14/14.00  
% 23.14/14.00  Ordering : KBO
% 23.14/14.00  
% 23.14/14.00  Simplification rules
% 23.14/14.00  ----------------------
% 23.14/14.00  #Subsume      : 1840
% 23.14/14.00  #Demod        : 18613
% 23.14/14.00  #Tautology    : 10541
% 23.14/14.00  #SimpNegUnit  : 527
% 23.14/14.00  #BackRed      : 131
% 23.14/14.00  
% 23.14/14.00  #Partial instantiations: 0
% 23.14/14.00  #Strategies tried      : 1
% 23.14/14.00  
% 23.14/14.00  Timing (in seconds)
% 23.14/14.00  ----------------------
% 23.14/14.01  Preprocessing        : 0.39
% 23.14/14.01  Parsing              : 0.20
% 23.14/14.01  CNF conversion       : 0.03
% 23.14/14.01  Main loop            : 12.78
% 23.14/14.01  Inferencing          : 1.58
% 23.14/14.01  Reduction            : 7.44
% 23.14/14.01  Demodulation         : 6.64
% 23.14/14.01  BG Simplification    : 0.18
% 23.14/14.01  Subsumption          : 2.96
% 23.14/14.01  Abstraction          : 0.29
% 23.14/14.01  MUC search           : 0.00
% 23.14/14.01  Cooper               : 0.00
% 23.14/14.01  Total                : 13.21
% 23.14/14.01  Index Insertion      : 0.00
% 23.14/14.01  Index Deletion       : 0.00
% 23.14/14.01  Index Matching       : 0.00
% 23.14/14.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
