%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 266 expanded)
%              Number of leaves         :   44 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 581 expanded)
%              Number of equality atoms :   82 ( 202 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_70,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_147,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_147])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_34,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_239,plain,(
    ! [B_87,A_88] :
      ( r1_xboole_0(k1_relat_1(B_87),A_88)
      | k9_relat_1(B_87,A_88) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_245,plain,(
    ! [A_88] :
      ( r1_xboole_0(k1_xboole_0,A_88)
      | k9_relat_1(k1_xboole_0,A_88) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_239])).

tff(c_248,plain,(
    ! [A_88] : r1_xboole_0(k1_xboole_0,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_34,c_245])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_339,plain,(
    ! [B_108,A_109] :
      ( k1_tarski(k1_funct_1(B_108,A_109)) = k2_relat_1(B_108)
      | k1_tarski(A_109) != k1_relat_1(B_108)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_310,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_320,plain,(
    ! [D_104] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_104) = k9_relat_1('#skF_4',D_104) ),
    inference(resolution,[status(thm)],[c_64,c_310])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_322,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_60])).

tff(c_345,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_322])).

tff(c_372,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_68,c_345])).

tff(c_406,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_250,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_258,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_250])).

tff(c_283,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k1_relset_1(A_98,B_99,C_100),k1_zfmisc_1(A_98))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_300,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_283])).

tff(c_305,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_300])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_309,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_305,c_28])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_425,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k1_enumset1(A_117,B_118,C_119) = D_120
      | k2_tarski(A_117,C_119) = D_120
      | k2_tarski(B_118,C_119) = D_120
      | k2_tarski(A_117,B_118) = D_120
      | k1_tarski(C_119) = D_120
      | k1_tarski(B_118) = D_120
      | k1_tarski(A_117) = D_120
      | k1_xboole_0 = D_120
      | ~ r1_tarski(D_120,k1_enumset1(A_117,B_118,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_443,plain,(
    ! [A_3,B_4,D_120] :
      ( k1_enumset1(A_3,A_3,B_4) = D_120
      | k2_tarski(A_3,B_4) = D_120
      | k2_tarski(A_3,B_4) = D_120
      | k2_tarski(A_3,A_3) = D_120
      | k1_tarski(B_4) = D_120
      | k1_tarski(A_3) = D_120
      | k1_tarski(A_3) = D_120
      | k1_xboole_0 = D_120
      | ~ r1_tarski(D_120,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_425])).

tff(c_734,plain,(
    ! [A_196,B_197,D_198] :
      ( k2_tarski(A_196,B_197) = D_198
      | k2_tarski(A_196,B_197) = D_198
      | k2_tarski(A_196,B_197) = D_198
      | k1_tarski(A_196) = D_198
      | k1_tarski(B_197) = D_198
      | k1_tarski(A_196) = D_198
      | k1_tarski(A_196) = D_198
      | k1_xboole_0 = D_198
      | ~ r1_tarski(D_198,k2_tarski(A_196,B_197)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_443])).

tff(c_760,plain,(
    ! [A_2,D_198] :
      ( k2_tarski(A_2,A_2) = D_198
      | k2_tarski(A_2,A_2) = D_198
      | k2_tarski(A_2,A_2) = D_198
      | k1_tarski(A_2) = D_198
      | k1_tarski(A_2) = D_198
      | k1_tarski(A_2) = D_198
      | k1_tarski(A_2) = D_198
      | k1_xboole_0 = D_198
      | ~ r1_tarski(D_198,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_734])).

tff(c_778,plain,(
    ! [A_199,D_200] :
      ( k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_tarski(A_199) = D_200
      | k1_xboole_0 = D_200
      | ~ r1_tarski(D_200,k1_tarski(A_199)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_760])).

tff(c_795,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_309,c_778])).

tff(c_808,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_406,c_406,c_406,c_406,c_406,c_406,c_795])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( k9_relat_1(B_18,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_825,plain,(
    ! [A_17] :
      ( k9_relat_1('#skF_4',A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_17)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_36])).

tff(c_831,plain,(
    ! [A_17] : k9_relat_1('#skF_4',A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_248,c_825])).

tff(c_833,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_322])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_833])).

tff(c_838,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_940,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_838])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  
% 3.23/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.47  %$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.47  
% 3.23/1.47  %Foreground sorts:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Background operators:
% 3.23/1.47  
% 3.23/1.47  
% 3.23/1.47  %Foreground operators:
% 3.23/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.23/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.23/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.23/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.47  
% 3.23/1.49  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.23/1.49  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.23/1.49  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.23/1.49  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.49  tff(f_80, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.23/1.49  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.23/1.49  tff(f_70, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.23/1.49  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.23/1.49  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.23/1.49  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.23/1.49  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.23/1.49  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.49  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.23/1.49  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.23/1.49  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.49  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.23/1.49  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.23/1.49  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.49  tff(c_147, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.49  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_147])).
% 3.23/1.49  tff(c_32, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/1.49  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.49  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.23/1.49  tff(c_46, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.49  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_46])).
% 3.23/1.49  tff(c_34, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.49  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.49  tff(c_239, plain, (![B_87, A_88]: (r1_xboole_0(k1_relat_1(B_87), A_88) | k9_relat_1(B_87, A_88)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.49  tff(c_245, plain, (![A_88]: (r1_xboole_0(k1_xboole_0, A_88) | k9_relat_1(k1_xboole_0, A_88)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_239])).
% 3.23/1.49  tff(c_248, plain, (![A_88]: (r1_xboole_0(k1_xboole_0, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_34, c_245])).
% 3.23/1.49  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.49  tff(c_339, plain, (![B_108, A_109]: (k1_tarski(k1_funct_1(B_108, A_109))=k2_relat_1(B_108) | k1_tarski(A_109)!=k1_relat_1(B_108) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.49  tff(c_310, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.23/1.49  tff(c_320, plain, (![D_104]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_104)=k9_relat_1('#skF_4', D_104))), inference(resolution, [status(thm)], [c_64, c_310])).
% 3.23/1.49  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.23/1.49  tff(c_322, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_60])).
% 3.23/1.49  tff(c_345, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_339, c_322])).
% 3.23/1.49  tff(c_372, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_68, c_345])).
% 3.23/1.49  tff(c_406, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_372])).
% 3.23/1.49  tff(c_250, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.23/1.49  tff(c_258, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_250])).
% 3.23/1.49  tff(c_283, plain, (![A_98, B_99, C_100]: (m1_subset_1(k1_relset_1(A_98, B_99, C_100), k1_zfmisc_1(A_98)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.23/1.49  tff(c_300, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_258, c_283])).
% 3.23/1.49  tff(c_305, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_300])).
% 3.23/1.49  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.23/1.49  tff(c_309, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_305, c_28])).
% 3.23/1.49  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.49  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.49  tff(c_425, plain, (![A_117, B_118, C_119, D_120]: (k1_enumset1(A_117, B_118, C_119)=D_120 | k2_tarski(A_117, C_119)=D_120 | k2_tarski(B_118, C_119)=D_120 | k2_tarski(A_117, B_118)=D_120 | k1_tarski(C_119)=D_120 | k1_tarski(B_118)=D_120 | k1_tarski(A_117)=D_120 | k1_xboole_0=D_120 | ~r1_tarski(D_120, k1_enumset1(A_117, B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.49  tff(c_443, plain, (![A_3, B_4, D_120]: (k1_enumset1(A_3, A_3, B_4)=D_120 | k2_tarski(A_3, B_4)=D_120 | k2_tarski(A_3, B_4)=D_120 | k2_tarski(A_3, A_3)=D_120 | k1_tarski(B_4)=D_120 | k1_tarski(A_3)=D_120 | k1_tarski(A_3)=D_120 | k1_xboole_0=D_120 | ~r1_tarski(D_120, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_425])).
% 3.23/1.49  tff(c_734, plain, (![A_196, B_197, D_198]: (k2_tarski(A_196, B_197)=D_198 | k2_tarski(A_196, B_197)=D_198 | k2_tarski(A_196, B_197)=D_198 | k1_tarski(A_196)=D_198 | k1_tarski(B_197)=D_198 | k1_tarski(A_196)=D_198 | k1_tarski(A_196)=D_198 | k1_xboole_0=D_198 | ~r1_tarski(D_198, k2_tarski(A_196, B_197)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_443])).
% 3.23/1.49  tff(c_760, plain, (![A_2, D_198]: (k2_tarski(A_2, A_2)=D_198 | k2_tarski(A_2, A_2)=D_198 | k2_tarski(A_2, A_2)=D_198 | k1_tarski(A_2)=D_198 | k1_tarski(A_2)=D_198 | k1_tarski(A_2)=D_198 | k1_tarski(A_2)=D_198 | k1_xboole_0=D_198 | ~r1_tarski(D_198, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_734])).
% 3.23/1.49  tff(c_778, plain, (![A_199, D_200]: (k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_tarski(A_199)=D_200 | k1_xboole_0=D_200 | ~r1_tarski(D_200, k1_tarski(A_199)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_760])).
% 3.23/1.49  tff(c_795, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_309, c_778])).
% 3.23/1.49  tff(c_808, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_406, c_406, c_406, c_406, c_406, c_406, c_406, c_795])).
% 3.23/1.49  tff(c_36, plain, (![B_18, A_17]: (k9_relat_1(B_18, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.49  tff(c_825, plain, (![A_17]: (k9_relat_1('#skF_4', A_17)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_17) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_36])).
% 3.23/1.49  tff(c_831, plain, (![A_17]: (k9_relat_1('#skF_4', A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_248, c_825])).
% 3.23/1.49  tff(c_833, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_831, c_322])).
% 3.23/1.49  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_833])).
% 3.23/1.49  tff(c_838, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_372])).
% 3.23/1.49  tff(c_940, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_838])).
% 3.23/1.49  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_940])).
% 3.23/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  Inference rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Ref     : 0
% 3.23/1.49  #Sup     : 187
% 3.23/1.49  #Fact    : 0
% 3.23/1.49  #Define  : 0
% 3.23/1.49  #Split   : 1
% 3.23/1.49  #Chain   : 0
% 3.23/1.49  #Close   : 0
% 3.23/1.49  
% 3.23/1.49  Ordering : KBO
% 3.23/1.49  
% 3.23/1.49  Simplification rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Subsume      : 16
% 3.23/1.49  #Demod        : 147
% 3.23/1.49  #Tautology    : 102
% 3.23/1.49  #SimpNegUnit  : 1
% 3.23/1.49  #BackRed      : 14
% 3.23/1.49  
% 3.23/1.49  #Partial instantiations: 0
% 3.23/1.49  #Strategies tried      : 1
% 3.23/1.49  
% 3.23/1.49  Timing (in seconds)
% 3.23/1.49  ----------------------
% 3.23/1.49  Preprocessing        : 0.34
% 3.23/1.49  Parsing              : 0.18
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.44
% 3.23/1.49  Inferencing          : 0.17
% 3.23/1.49  Reduction            : 0.14
% 3.23/1.49  Demodulation         : 0.10
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.07
% 3.23/1.49  Abstraction          : 0.03
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.81
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
