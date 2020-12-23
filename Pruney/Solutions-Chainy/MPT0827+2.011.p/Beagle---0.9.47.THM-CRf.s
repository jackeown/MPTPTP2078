%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 181 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 308 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9494,plain,(
    ! [A_461,B_462,C_463] :
      ( k2_relset_1(A_461,B_462,C_463) = k2_relat_1(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9503,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_9494])).

tff(c_631,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_640,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_631])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_641,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_106])).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_169,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_175,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_169])).

tff(c_179,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_175])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_197,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k2_zfmisc_1(k1_relat_1(A_53),k2_relat_1(A_53)))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_206,plain,(
    ! [A_20] :
      ( r1_tarski(k6_relat_1(A_20),k2_zfmisc_1(A_20,k2_relat_1(k6_relat_1(A_20))))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_215,plain,(
    ! [A_20] : r1_tarski(k6_relat_1(A_20),k2_zfmisc_1(A_20,A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_206])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_383,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_403,plain,(
    ! [A_83,B_84,A_85] :
      ( v5_relat_1(A_83,B_84)
      | ~ r1_tarski(A_83,k2_zfmisc_1(A_85,B_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_383])).

tff(c_431,plain,(
    ! [A_86] : v5_relat_1(k6_relat_1(A_86),A_86) ),
    inference(resolution,[status(thm)],[c_215,c_403])).

tff(c_322,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k2_relat_1(B_66),A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_342,plain,(
    ! [A_20,A_67] :
      ( r1_tarski(A_20,A_67)
      | ~ v5_relat_1(k6_relat_1(A_20),A_67)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_322])).

tff(c_349,plain,(
    ! [A_20,A_67] :
      ( r1_tarski(A_20,A_67)
      | ~ v5_relat_1(k6_relat_1(A_20),A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_342])).

tff(c_455,plain,(
    ! [A_88] : r1_tarski(A_88,A_88) ),
    inference(resolution,[status(thm)],[c_431,c_349])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_485,plain,(
    ! [A_88] : k2_xboole_0(A_88,A_88) = A_88 ),
    inference(resolution,[status(thm)],[c_455,c_6])).

tff(c_44,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_148,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,k2_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1628,plain,(
    ! [A_171,C_172,B_173] :
      ( k2_xboole_0(A_171,k2_xboole_0(C_172,B_173)) = k2_xboole_0(C_172,B_173)
      | ~ r1_tarski(A_171,B_173) ) ),
    inference(resolution,[status(thm)],[c_148,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_45,B_2,A_1] :
      ( r1_tarski(A_45,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_45,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_4091,plain,(
    ! [A_289,C_290,B_291,A_292] :
      ( r1_tarski(A_289,k2_xboole_0(C_290,B_291))
      | ~ r1_tarski(A_289,A_292)
      | ~ r1_tarski(A_292,B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1628,c_163])).

tff(c_4396,plain,(
    ! [C_296,B_297] :
      ( r1_tarski(k6_relat_1('#skF_3'),k2_xboole_0(C_296,B_297))
      | ~ r1_tarski('#skF_4',B_297) ) ),
    inference(resolution,[status(thm)],[c_44,c_4091])).

tff(c_4614,plain,(
    ! [A_302] :
      ( r1_tarski(k6_relat_1('#skF_3'),A_302)
      | ~ r1_tarski('#skF_4',A_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_4396])).

tff(c_393,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_401,plain,(
    ! [A_8,A_81,B_82] :
      ( v4_relat_1(A_8,A_81)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_10,c_393])).

tff(c_8895,plain,(
    ! [A_397,B_398] :
      ( v4_relat_1(k6_relat_1('#skF_3'),A_397)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_397,B_398)) ) ),
    inference(resolution,[status(thm)],[c_4614,c_401])).

tff(c_8907,plain,
    ( v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_8895])).

tff(c_8918,plain,(
    v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_8907])).

tff(c_298,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v4_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_315,plain,(
    ! [A_20,A_65] :
      ( r1_tarski(A_20,A_65)
      | ~ v4_relat_1(k6_relat_1(A_20),A_65)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_321,plain,(
    ! [A_20,A_65] :
      ( r1_tarski(A_20,A_65)
      | ~ v4_relat_1(k6_relat_1(A_20),A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_315])).

tff(c_8931,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8918,c_321])).

tff(c_8940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_8931])).

tff(c_8941,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_9504,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9503,c_8941])).

tff(c_8982,plain,(
    ! [B_403,A_404] :
      ( v1_relat_1(B_403)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_404))
      | ~ v1_relat_1(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8988,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_8982])).

tff(c_8992,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8988])).

tff(c_9158,plain,(
    ! [A_431] :
      ( r1_tarski(A_431,k2_zfmisc_1(k1_relat_1(A_431),k2_relat_1(A_431)))
      | ~ v1_relat_1(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9178,plain,(
    ! [A_20] :
      ( r1_tarski(k6_relat_1(A_20),k2_zfmisc_1(A_20,k2_relat_1(k6_relat_1(A_20))))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9158])).

tff(c_9190,plain,(
    ! [A_20] : r1_tarski(k6_relat_1(A_20),k2_zfmisc_1(A_20,A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_9178])).

tff(c_9235,plain,(
    ! [C_436,B_437,A_438] :
      ( v5_relat_1(C_436,B_437)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_438,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9283,plain,(
    ! [A_443,B_444,A_445] :
      ( v5_relat_1(A_443,B_444)
      | ~ r1_tarski(A_443,k2_zfmisc_1(A_445,B_444)) ) ),
    inference(resolution,[status(thm)],[c_10,c_9235])).

tff(c_9312,plain,(
    ! [A_447] : v5_relat_1(k6_relat_1(A_447),A_447) ),
    inference(resolution,[status(thm)],[c_9190,c_9283])).

tff(c_9245,plain,(
    ! [B_439,A_440] :
      ( r1_tarski(k2_relat_1(B_439),A_440)
      | ~ v5_relat_1(B_439,A_440)
      | ~ v1_relat_1(B_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_9269,plain,(
    ! [A_20,A_440] :
      ( r1_tarski(A_20,A_440)
      | ~ v5_relat_1(k6_relat_1(A_20),A_440)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9245])).

tff(c_9277,plain,(
    ! [A_20,A_440] :
      ( r1_tarski(A_20,A_440)
      | ~ v5_relat_1(k6_relat_1(A_20),A_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9269])).

tff(c_9317,plain,(
    ! [A_448] : r1_tarski(A_448,A_448) ),
    inference(resolution,[status(thm)],[c_9312,c_9277])).

tff(c_9357,plain,(
    ! [A_448] : k2_xboole_0(A_448,A_448) = A_448 ),
    inference(resolution,[status(thm)],[c_9317,c_6])).

tff(c_9017,plain,(
    ! [A_407,C_408,B_409] :
      ( r1_tarski(A_407,k2_xboole_0(C_408,B_409))
      | ~ r1_tarski(A_407,B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10025,plain,(
    ! [A_498,C_499,B_500] :
      ( k2_xboole_0(A_498,k2_xboole_0(C_499,B_500)) = k2_xboole_0(C_499,B_500)
      | ~ r1_tarski(A_498,B_500) ) ),
    inference(resolution,[status(thm)],[c_9017,c_6])).

tff(c_9035,plain,(
    ! [A_407,B_2,A_1] :
      ( r1_tarski(A_407,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_407,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9017])).

tff(c_14394,plain,(
    ! [A_707,C_708,B_709,A_710] :
      ( r1_tarski(A_707,k2_xboole_0(C_708,B_709))
      | ~ r1_tarski(A_707,A_710)
      | ~ r1_tarski(A_710,B_709) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10025,c_9035])).

tff(c_14745,plain,(
    ! [C_714,B_715] :
      ( r1_tarski(k6_relat_1('#skF_3'),k2_xboole_0(C_714,B_715))
      | ~ r1_tarski('#skF_4',B_715) ) ),
    inference(resolution,[status(thm)],[c_44,c_14394])).

tff(c_14952,plain,(
    ! [A_717] :
      ( r1_tarski(k6_relat_1('#skF_3'),A_717)
      | ~ r1_tarski('#skF_4',A_717) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9357,c_14745])).

tff(c_9243,plain,(
    ! [A_8,B_437,A_438] :
      ( v5_relat_1(A_8,B_437)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_438,B_437)) ) ),
    inference(resolution,[status(thm)],[c_10,c_9235])).

tff(c_22832,plain,(
    ! [B_899,A_900] :
      ( v5_relat_1(k6_relat_1('#skF_3'),B_899)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_900,B_899)) ) ),
    inference(resolution,[status(thm)],[c_14952,c_9243])).

tff(c_22844,plain,
    ( v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_22832])).

tff(c_22856,plain,(
    v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8992,c_22844])).

tff(c_22872,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22856,c_9277])).

tff(c_22881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9504,c_22872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.34/4.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.48  
% 11.34/4.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/4.48  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.47/4.48  
% 11.47/4.48  %Foreground sorts:
% 11.47/4.48  
% 11.47/4.48  
% 11.47/4.48  %Background operators:
% 11.47/4.48  
% 11.47/4.48  
% 11.47/4.48  %Foreground operators:
% 11.47/4.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.47/4.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.47/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.47/4.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.47/4.48  tff('#skF_2', type, '#skF_2': $i).
% 11.47/4.48  tff('#skF_3', type, '#skF_3': $i).
% 11.47/4.48  tff('#skF_1', type, '#skF_1': $i).
% 11.47/4.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.47/4.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.47/4.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.47/4.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.47/4.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.47/4.48  tff('#skF_4', type, '#skF_4': $i).
% 11.47/4.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.47/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.47/4.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.47/4.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.47/4.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.47/4.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.47/4.48  
% 11.47/4.50  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 11.47/4.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.47/4.50  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.47/4.50  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.47/4.50  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.47/4.50  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 11.47/4.50  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.47/4.50  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.47/4.50  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.47/4.50  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.47/4.50  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.47/4.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.47/4.50  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 11.47/4.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.47/4.50  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.47/4.50  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.47/4.50  tff(c_9494, plain, (![A_461, B_462, C_463]: (k2_relset_1(A_461, B_462, C_463)=k2_relat_1(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.47/4.50  tff(c_9503, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_9494])).
% 11.47/4.50  tff(c_631, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.47/4.50  tff(c_640, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_631])).
% 11.47/4.50  tff(c_42, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.47/4.50  tff(c_106, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 11.47/4.50  tff(c_641, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_106])).
% 11.47/4.50  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.47/4.50  tff(c_169, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.47/4.50  tff(c_175, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_169])).
% 11.47/4.50  tff(c_179, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_175])).
% 11.47/4.50  tff(c_24, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.47/4.50  tff(c_30, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.47/4.50  tff(c_28, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.47/4.50  tff(c_26, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.47/4.50  tff(c_197, plain, (![A_53]: (r1_tarski(A_53, k2_zfmisc_1(k1_relat_1(A_53), k2_relat_1(A_53))) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.47/4.50  tff(c_206, plain, (![A_20]: (r1_tarski(k6_relat_1(A_20), k2_zfmisc_1(A_20, k2_relat_1(k6_relat_1(A_20)))) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_197])).
% 11.47/4.50  tff(c_215, plain, (![A_20]: (r1_tarski(k6_relat_1(A_20), k2_zfmisc_1(A_20, A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_206])).
% 11.47/4.50  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.47/4.50  tff(c_383, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.47/4.50  tff(c_403, plain, (![A_83, B_84, A_85]: (v5_relat_1(A_83, B_84) | ~r1_tarski(A_83, k2_zfmisc_1(A_85, B_84)))), inference(resolution, [status(thm)], [c_10, c_383])).
% 11.47/4.50  tff(c_431, plain, (![A_86]: (v5_relat_1(k6_relat_1(A_86), A_86))), inference(resolution, [status(thm)], [c_215, c_403])).
% 11.47/4.50  tff(c_322, plain, (![B_66, A_67]: (r1_tarski(k2_relat_1(B_66), A_67) | ~v5_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.50  tff(c_342, plain, (![A_20, A_67]: (r1_tarski(A_20, A_67) | ~v5_relat_1(k6_relat_1(A_20), A_67) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_322])).
% 11.47/4.50  tff(c_349, plain, (![A_20, A_67]: (r1_tarski(A_20, A_67) | ~v5_relat_1(k6_relat_1(A_20), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_342])).
% 11.47/4.50  tff(c_455, plain, (![A_88]: (r1_tarski(A_88, A_88))), inference(resolution, [status(thm)], [c_431, c_349])).
% 11.47/4.50  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.47/4.50  tff(c_485, plain, (![A_88]: (k2_xboole_0(A_88, A_88)=A_88)), inference(resolution, [status(thm)], [c_455, c_6])).
% 11.47/4.50  tff(c_44, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.47/4.50  tff(c_148, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, k2_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_1628, plain, (![A_171, C_172, B_173]: (k2_xboole_0(A_171, k2_xboole_0(C_172, B_173))=k2_xboole_0(C_172, B_173) | ~r1_tarski(A_171, B_173))), inference(resolution, [status(thm)], [c_148, c_6])).
% 11.47/4.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.47/4.50  tff(c_163, plain, (![A_45, B_2, A_1]: (r1_tarski(A_45, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_45, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_148])).
% 11.47/4.50  tff(c_4091, plain, (![A_289, C_290, B_291, A_292]: (r1_tarski(A_289, k2_xboole_0(C_290, B_291)) | ~r1_tarski(A_289, A_292) | ~r1_tarski(A_292, B_291))), inference(superposition, [status(thm), theory('equality')], [c_1628, c_163])).
% 11.47/4.50  tff(c_4396, plain, (![C_296, B_297]: (r1_tarski(k6_relat_1('#skF_3'), k2_xboole_0(C_296, B_297)) | ~r1_tarski('#skF_4', B_297))), inference(resolution, [status(thm)], [c_44, c_4091])).
% 11.47/4.50  tff(c_4614, plain, (![A_302]: (r1_tarski(k6_relat_1('#skF_3'), A_302) | ~r1_tarski('#skF_4', A_302))), inference(superposition, [status(thm), theory('equality')], [c_485, c_4396])).
% 11.47/4.50  tff(c_393, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.47/4.50  tff(c_401, plain, (![A_8, A_81, B_82]: (v4_relat_1(A_8, A_81) | ~r1_tarski(A_8, k2_zfmisc_1(A_81, B_82)))), inference(resolution, [status(thm)], [c_10, c_393])).
% 11.47/4.50  tff(c_8895, plain, (![A_397, B_398]: (v4_relat_1(k6_relat_1('#skF_3'), A_397) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_397, B_398)))), inference(resolution, [status(thm)], [c_4614, c_401])).
% 11.47/4.50  tff(c_8907, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_8895])).
% 11.47/4.50  tff(c_8918, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_8907])).
% 11.47/4.50  tff(c_298, plain, (![B_64, A_65]: (r1_tarski(k1_relat_1(B_64), A_65) | ~v4_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.47/4.50  tff(c_315, plain, (![A_20, A_65]: (r1_tarski(A_20, A_65) | ~v4_relat_1(k6_relat_1(A_20), A_65) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_298])).
% 11.47/4.50  tff(c_321, plain, (![A_20, A_65]: (r1_tarski(A_20, A_65) | ~v4_relat_1(k6_relat_1(A_20), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_315])).
% 11.47/4.50  tff(c_8931, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8918, c_321])).
% 11.47/4.50  tff(c_8940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_641, c_8931])).
% 11.47/4.50  tff(c_8941, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 11.47/4.50  tff(c_9504, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9503, c_8941])).
% 11.47/4.50  tff(c_8982, plain, (![B_403, A_404]: (v1_relat_1(B_403) | ~m1_subset_1(B_403, k1_zfmisc_1(A_404)) | ~v1_relat_1(A_404))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.47/4.50  tff(c_8988, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_8982])).
% 11.47/4.50  tff(c_8992, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8988])).
% 11.47/4.50  tff(c_9158, plain, (![A_431]: (r1_tarski(A_431, k2_zfmisc_1(k1_relat_1(A_431), k2_relat_1(A_431))) | ~v1_relat_1(A_431))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.47/4.50  tff(c_9178, plain, (![A_20]: (r1_tarski(k6_relat_1(A_20), k2_zfmisc_1(A_20, k2_relat_1(k6_relat_1(A_20)))) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9158])).
% 11.47/4.50  tff(c_9190, plain, (![A_20]: (r1_tarski(k6_relat_1(A_20), k2_zfmisc_1(A_20, A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_9178])).
% 11.47/4.50  tff(c_9235, plain, (![C_436, B_437, A_438]: (v5_relat_1(C_436, B_437) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_438, B_437))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.47/4.50  tff(c_9283, plain, (![A_443, B_444, A_445]: (v5_relat_1(A_443, B_444) | ~r1_tarski(A_443, k2_zfmisc_1(A_445, B_444)))), inference(resolution, [status(thm)], [c_10, c_9235])).
% 11.47/4.50  tff(c_9312, plain, (![A_447]: (v5_relat_1(k6_relat_1(A_447), A_447))), inference(resolution, [status(thm)], [c_9190, c_9283])).
% 11.47/4.50  tff(c_9245, plain, (![B_439, A_440]: (r1_tarski(k2_relat_1(B_439), A_440) | ~v5_relat_1(B_439, A_440) | ~v1_relat_1(B_439))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.47/4.50  tff(c_9269, plain, (![A_20, A_440]: (r1_tarski(A_20, A_440) | ~v5_relat_1(k6_relat_1(A_20), A_440) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9245])).
% 11.47/4.50  tff(c_9277, plain, (![A_20, A_440]: (r1_tarski(A_20, A_440) | ~v5_relat_1(k6_relat_1(A_20), A_440))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9269])).
% 11.47/4.50  tff(c_9317, plain, (![A_448]: (r1_tarski(A_448, A_448))), inference(resolution, [status(thm)], [c_9312, c_9277])).
% 11.47/4.50  tff(c_9357, plain, (![A_448]: (k2_xboole_0(A_448, A_448)=A_448)), inference(resolution, [status(thm)], [c_9317, c_6])).
% 11.47/4.50  tff(c_9017, plain, (![A_407, C_408, B_409]: (r1_tarski(A_407, k2_xboole_0(C_408, B_409)) | ~r1_tarski(A_407, B_409))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.47/4.50  tff(c_10025, plain, (![A_498, C_499, B_500]: (k2_xboole_0(A_498, k2_xboole_0(C_499, B_500))=k2_xboole_0(C_499, B_500) | ~r1_tarski(A_498, B_500))), inference(resolution, [status(thm)], [c_9017, c_6])).
% 11.47/4.50  tff(c_9035, plain, (![A_407, B_2, A_1]: (r1_tarski(A_407, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_407, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9017])).
% 11.47/4.50  tff(c_14394, plain, (![A_707, C_708, B_709, A_710]: (r1_tarski(A_707, k2_xboole_0(C_708, B_709)) | ~r1_tarski(A_707, A_710) | ~r1_tarski(A_710, B_709))), inference(superposition, [status(thm), theory('equality')], [c_10025, c_9035])).
% 11.47/4.50  tff(c_14745, plain, (![C_714, B_715]: (r1_tarski(k6_relat_1('#skF_3'), k2_xboole_0(C_714, B_715)) | ~r1_tarski('#skF_4', B_715))), inference(resolution, [status(thm)], [c_44, c_14394])).
% 11.47/4.50  tff(c_14952, plain, (![A_717]: (r1_tarski(k6_relat_1('#skF_3'), A_717) | ~r1_tarski('#skF_4', A_717))), inference(superposition, [status(thm), theory('equality')], [c_9357, c_14745])).
% 11.47/4.50  tff(c_9243, plain, (![A_8, B_437, A_438]: (v5_relat_1(A_8, B_437) | ~r1_tarski(A_8, k2_zfmisc_1(A_438, B_437)))), inference(resolution, [status(thm)], [c_10, c_9235])).
% 11.47/4.50  tff(c_22832, plain, (![B_899, A_900]: (v5_relat_1(k6_relat_1('#skF_3'), B_899) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_900, B_899)))), inference(resolution, [status(thm)], [c_14952, c_9243])).
% 11.47/4.50  tff(c_22844, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_22832])).
% 11.47/4.50  tff(c_22856, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8992, c_22844])).
% 11.47/4.50  tff(c_22872, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22856, c_9277])).
% 11.47/4.50  tff(c_22881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9504, c_22872])).
% 11.47/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/4.50  
% 11.47/4.50  Inference rules
% 11.47/4.50  ----------------------
% 11.47/4.50  #Ref     : 0
% 11.47/4.50  #Sup     : 5437
% 11.47/4.50  #Fact    : 0
% 11.47/4.50  #Define  : 0
% 11.47/4.50  #Split   : 44
% 11.47/4.50  #Chain   : 0
% 11.47/4.50  #Close   : 0
% 11.47/4.50  
% 11.47/4.50  Ordering : KBO
% 11.47/4.50  
% 11.47/4.50  Simplification rules
% 11.47/4.50  ----------------------
% 11.47/4.50  #Subsume      : 2042
% 11.47/4.50  #Demod        : 2804
% 11.47/4.50  #Tautology    : 1269
% 11.47/4.50  #SimpNegUnit  : 3
% 11.47/4.50  #BackRed      : 6
% 11.47/4.50  
% 11.47/4.50  #Partial instantiations: 0
% 11.47/4.50  #Strategies tried      : 1
% 11.47/4.50  
% 11.47/4.50  Timing (in seconds)
% 11.47/4.50  ----------------------
% 11.47/4.50  Preprocessing        : 0.34
% 11.47/4.50  Parsing              : 0.19
% 11.47/4.50  CNF conversion       : 0.02
% 11.47/4.51  Main loop            : 3.33
% 11.47/4.51  Inferencing          : 0.85
% 11.47/4.51  Reduction            : 1.36
% 11.47/4.51  Demodulation         : 1.03
% 11.47/4.51  BG Simplification    : 0.07
% 11.47/4.51  Subsumption          : 0.84
% 11.47/4.51  Abstraction          : 0.10
% 11.47/4.51  MUC search           : 0.00
% 11.47/4.51  Cooper               : 0.00
% 11.47/4.51  Total                : 3.71
% 11.47/4.51  Index Insertion      : 0.00
% 11.47/4.51  Index Deletion       : 0.00
% 11.47/4.51  Index Matching       : 0.00
% 11.47/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
