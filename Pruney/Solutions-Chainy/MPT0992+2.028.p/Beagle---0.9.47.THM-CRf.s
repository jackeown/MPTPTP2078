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
% DateTime   : Thu Dec  3 10:13:35 EST 2020

% Result     : Theorem 10.23s
% Output     : CNFRefutation 10.45s
% Verified   : 
% Statistics : Number of formulae       :  177 (2952 expanded)
%              Number of leaves         :   37 ( 933 expanded)
%              Depth                    :   14
%              Number of atoms          :  312 (9446 expanded)
%              Number of equality atoms :   74 (3719 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1061,plain,(
    ! [C_177,A_178,B_179] :
      ( v1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1074,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1061])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10786,plain,(
    ! [A_930,B_931,C_932] :
      ( k1_relset_1(A_930,B_931,C_932) = k1_relat_1(C_932)
      | ~ m1_subset_1(C_932,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10805,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_10786])).

tff(c_11545,plain,(
    ! [B_1020,A_1021,C_1022] :
      ( k1_xboole_0 = B_1020
      | k1_relset_1(A_1021,B_1020,C_1022) = A_1021
      | ~ v1_funct_2(C_1022,A_1021,B_1020)
      | ~ m1_subset_1(C_1022,k1_zfmisc_1(k2_zfmisc_1(A_1021,B_1020))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11558,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_11545])).

tff(c_11572,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10805,c_11558])).

tff(c_11573,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_11572])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11588,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11573,c_32])).

tff(c_11643,plain,(
    ! [A_1025] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1025)) = A_1025
      | ~ r1_tarski(A_1025,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_11588])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_11411,plain,(
    ! [A_1010,B_1011,C_1012,D_1013] :
      ( k2_partfun1(A_1010,B_1011,C_1012,D_1013) = k7_relat_1(C_1012,D_1013)
      | ~ m1_subset_1(C_1012,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011)))
      | ~ v1_funct_1(C_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_11420,plain,(
    ! [D_1013] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1013) = k7_relat_1('#skF_4',D_1013)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_11411])).

tff(c_11432,plain,(
    ! [D_1013] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1013) = k7_relat_1('#skF_4',D_1013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11420])).

tff(c_2082,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( k2_partfun1(A_310,B_311,C_312,D_313) = k7_relat_1(C_312,D_313)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ v1_funct_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2089,plain,(
    ! [D_313] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_313) = k7_relat_1('#skF_4',D_313)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_2082])).

tff(c_2098,plain,(
    ! [D_313] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_313) = k7_relat_1('#skF_4',D_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2089])).

tff(c_2473,plain,(
    ! [A_333,B_334,C_335,D_336] :
      ( m1_subset_1(k2_partfun1(A_333,B_334,C_335,D_336),k1_zfmisc_1(k2_zfmisc_1(A_333,B_334)))
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334)))
      | ~ v1_funct_1(C_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2501,plain,(
    ! [D_313] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_313),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_2473])).

tff(c_2521,plain,(
    ! [D_337] : m1_subset_1(k7_relat_1('#skF_4',D_337),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2501])).

tff(c_36,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2561,plain,(
    ! [D_337] : v5_relat_1(k7_relat_1('#skF_4',D_337),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2521,c_36])).

tff(c_34,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2562,plain,(
    ! [D_337] : v1_relat_1(k7_relat_1('#skF_4',D_337)) ),
    inference(resolution,[status(thm)],[c_2521,c_34])).

tff(c_24,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1890,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( v1_funct_1(k2_partfun1(A_287,B_288,C_289,D_290))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1895,plain,(
    ! [D_290] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_290))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_1890])).

tff(c_1903,plain,(
    ! [D_290] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_290)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1895])).

tff(c_2099,plain,(
    ! [D_290] : v1_funct_1(k7_relat_1('#skF_4',D_290)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_1903])).

tff(c_1610,plain,(
    ! [A_250,B_251,C_252] :
      ( k1_relset_1(A_250,B_251,C_252) = k1_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1625,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1610])).

tff(c_2156,plain,(
    ! [B_320,A_321,C_322] :
      ( k1_xboole_0 = B_320
      | k1_relset_1(A_321,B_320,C_322) = A_321
      | ~ v1_funct_2(C_322,A_321,B_320)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_321,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2166,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_2156])).

tff(c_2177,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1625,c_2166])).

tff(c_2178,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2177])).

tff(c_2193,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_32])).

tff(c_2203,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_2193])).

tff(c_1992,plain,(
    ! [B_304,A_305] :
      ( m1_subset_1(B_304,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_304),A_305)))
      | ~ r1_tarski(k2_relat_1(B_304),A_305)
      | ~ v1_funct_1(B_304)
      | ~ v1_relat_1(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5994,plain,(
    ! [B_593,A_594] :
      ( r1_tarski(B_593,k2_zfmisc_1(k1_relat_1(B_593),A_594))
      | ~ r1_tarski(k2_relat_1(B_593),A_594)
      | ~ v1_funct_1(B_593)
      | ~ v1_relat_1(B_593) ) ),
    inference(resolution,[status(thm)],[c_1992,c_18])).

tff(c_6058,plain,(
    ! [A_17,A_594] :
      ( r1_tarski(k7_relat_1('#skF_4',A_17),k2_zfmisc_1(A_17,A_594))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_17)),A_594)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_17))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_17))
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_5994])).

tff(c_7418,plain,(
    ! [A_692,A_693] :
      ( r1_tarski(k7_relat_1('#skF_4',A_692),k2_zfmisc_1(A_692,A_693))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_692)),A_693)
      | ~ r1_tarski(A_692,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2099,c_6058])).

tff(c_7426,plain,(
    ! [A_692,A_9] :
      ( r1_tarski(k7_relat_1('#skF_4',A_692),k2_zfmisc_1(A_692,A_9))
      | ~ r1_tarski(A_692,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_692),A_9)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_692)) ) ),
    inference(resolution,[status(thm)],[c_24,c_7418])).

tff(c_10179,plain,(
    ! [A_858,A_859] :
      ( r1_tarski(k7_relat_1('#skF_4',A_858),k2_zfmisc_1(A_858,A_859))
      | ~ r1_tarski(A_858,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_858),A_859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_7426])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1037,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( v1_funct_1(k2_partfun1(A_171,B_172,C_173,D_174))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1042,plain,(
    ! [D_174] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_174))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_1037])).

tff(c_1050,plain,(
    ! [D_174] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_174)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1042])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_157])).

tff(c_1054,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1112,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1303,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_1112])).

tff(c_2100,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_1303])).

tff(c_10194,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10179,c_2100])).

tff(c_10232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2561,c_70,c_10194])).

tff(c_10234,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_10803,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10234,c_10786])).

tff(c_11435,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11432,c_11432,c_10803])).

tff(c_10233,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_11442,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11432,c_10233])).

tff(c_11441,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11432,c_10234])).

tff(c_48,plain,(
    ! [B_29,C_30,A_28] :
      ( k1_xboole_0 = B_29
      | v1_funct_2(C_30,A_28,B_29)
      | k1_relset_1(A_28,B_29,C_30) != A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11500,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_11441,c_48])).

tff(c_11522,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11442,c_84,c_11500])).

tff(c_11540,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11435,c_11522])).

tff(c_11652,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11643,c_11540])).

tff(c_11694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11652])).

tff(c_11695,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11710,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_16])).

tff(c_11696,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11702,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11696])).

tff(c_11720,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11710,c_11702,c_72])).

tff(c_11790,plain,(
    ! [A_1037,B_1038] :
      ( r1_tarski(A_1037,B_1038)
      | ~ m1_subset_1(A_1037,k1_zfmisc_1(B_1038)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11794,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_11720,c_11790])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11740,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_10])).

tff(c_11798,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11794,c_11740])).

tff(c_11703,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11702,c_74])).

tff(c_13098,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11703])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11697,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_8])).

tff(c_13102,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11697])).

tff(c_13099,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11720])).

tff(c_13101,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11710])).

tff(c_14504,plain,(
    ! [A_1399,B_1400,C_1401,D_1402] :
      ( m1_subset_1(k2_partfun1(A_1399,B_1400,C_1401,D_1402),k1_zfmisc_1(k2_zfmisc_1(A_1399,B_1400)))
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k2_zfmisc_1(A_1399,B_1400)))
      | ~ v1_funct_1(C_1401) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16282,plain,(
    ! [A_1565,B_1566,C_1567,D_1568] :
      ( v5_relat_1(k2_partfun1(A_1565,B_1566,C_1567,D_1568),B_1566)
      | ~ m1_subset_1(C_1567,k1_zfmisc_1(k2_zfmisc_1(A_1565,B_1566)))
      | ~ v1_funct_1(C_1567) ) ),
    inference(resolution,[status(thm)],[c_14504,c_36])).

tff(c_16297,plain,(
    ! [B_1569,C_1570,D_1571] :
      ( v5_relat_1(k2_partfun1('#skF_4',B_1569,C_1570,D_1571),B_1569)
      | ~ m1_subset_1(C_1570,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1570) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13101,c_16282])).

tff(c_15405,plain,(
    ! [A_1464,B_1465,C_1466,D_1467] :
      ( v1_relat_1(k2_partfun1(A_1464,B_1465,C_1466,D_1467))
      | ~ m1_subset_1(C_1466,k1_zfmisc_1(k2_zfmisc_1(A_1464,B_1465)))
      | ~ v1_funct_1(C_1466) ) ),
    inference(resolution,[status(thm)],[c_14504,c_34])).

tff(c_15420,plain,(
    ! [B_1468,C_1469,D_1470] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1468,C_1469,D_1470))
      | ~ m1_subset_1(C_1469,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13101,c_15405])).

tff(c_15424,plain,(
    ! [B_1468,D_1470] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1468,'#skF_4',D_1470))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13099,c_15420])).

tff(c_15431,plain,(
    ! [B_1468,D_1470] : v1_relat_1(k2_partfun1('#skF_4',B_1468,'#skF_4',D_1470)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15424])).

tff(c_13852,plain,(
    ! [A_1312,B_1313,C_1314,D_1315] :
      ( v1_funct_1(k2_partfun1(A_1312,B_1313,C_1314,D_1315))
      | ~ m1_subset_1(C_1314,k1_zfmisc_1(k2_zfmisc_1(A_1312,B_1313)))
      | ~ v1_funct_1(C_1314) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14372,plain,(
    ! [B_1382,C_1383,D_1384] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1382,C_1383,D_1384))
      | ~ m1_subset_1(C_1383,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13101,c_13852])).

tff(c_14374,plain,(
    ! [B_1382,D_1384] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_1382,'#skF_4',D_1384))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13099,c_14372])).

tff(c_14380,plain,(
    ! [B_1382,D_1384] : v1_funct_1(k2_partfun1('#skF_4',B_1382,'#skF_4',D_1384)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14374])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11721,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_14])).

tff(c_13097,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11721])).

tff(c_13992,plain,(
    ! [B_1336,A_1337] :
      ( m1_subset_1(B_1336,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1336),A_1337)))
      | ~ r1_tarski(k2_relat_1(B_1336),A_1337)
      | ~ v1_funct_1(B_1336)
      | ~ v1_relat_1(B_1336) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14411,plain,(
    ! [B_1395] :
      ( m1_subset_1(B_1395,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_1395),'#skF_4')
      | ~ v1_funct_1(B_1395)
      | ~ v1_relat_1(B_1395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13097,c_13992])).

tff(c_14422,plain,(
    ! [B_1396] :
      ( m1_subset_1(B_1396,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_1396)
      | ~ v5_relat_1(B_1396,'#skF_4')
      | ~ v1_relat_1(B_1396) ) ),
    inference(resolution,[status(thm)],[c_24,c_14411])).

tff(c_11807,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11720])).

tff(c_11805,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11721])).

tff(c_12743,plain,(
    ! [A_1168,B_1169,C_1170,D_1171] :
      ( v1_funct_1(k2_partfun1(A_1168,B_1169,C_1170,D_1171))
      | ~ m1_subset_1(C_1170,k1_zfmisc_1(k2_zfmisc_1(A_1168,B_1169)))
      | ~ v1_funct_1(C_1170) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_13060,plain,(
    ! [A_1206,C_1207,D_1208] :
      ( v1_funct_1(k2_partfun1(A_1206,'#skF_4',C_1207,D_1208))
      | ~ m1_subset_1(C_1207,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11805,c_12743])).

tff(c_13062,plain,(
    ! [A_1206,D_1208] :
      ( v1_funct_1(k2_partfun1(A_1206,'#skF_4','#skF_4',D_1208))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11807,c_13060])).

tff(c_13068,plain,(
    ! [A_1206,D_1208] : v1_funct_1(k2_partfun1(A_1206,'#skF_4','#skF_4',D_1208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13062])).

tff(c_11741,plain,(
    ! [A_1031] :
      ( A_1031 = '#skF_1'
      | ~ r1_tarski(A_1031,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11695,c_11695,c_10])).

tff(c_11757,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_70,c_11741])).

tff(c_11799,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11757,c_11702,c_11757,c_11757,c_11702,c_11702,c_11757,c_11721,c_11702,c_11702,c_66])).

tff(c_11800,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_11799])).

tff(c_11906,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11798,c_11800])).

tff(c_13090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13068,c_11906])).

tff(c_13091,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11799])).

tff(c_13296,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11798,c_11798,c_11798,c_11798,c_11798,c_11798,c_11798,c_11798,c_13091])).

tff(c_13297,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13296])).

tff(c_14437,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14422,c_13297])).

tff(c_14452,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14380,c_14437])).

tff(c_14859,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14452])).

tff(c_15435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15431,c_14859])).

tff(c_15436,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_14452])).

tff(c_16306,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16297,c_15436])).

tff(c_16337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13099,c_16306])).

tff(c_16339,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13296])).

tff(c_16347,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16339,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16352,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16347,c_2])).

tff(c_16360,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13102,c_16352])).

tff(c_16338,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_13296])).

tff(c_16365,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16360,c_16338])).

tff(c_16372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13098,c_16365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.23/3.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.23/3.69  
% 10.23/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.23/3.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.23/3.69  
% 10.23/3.69  %Foreground sorts:
% 10.23/3.69  
% 10.23/3.69  
% 10.23/3.69  %Background operators:
% 10.23/3.69  
% 10.23/3.69  
% 10.23/3.69  %Foreground operators:
% 10.23/3.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.23/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.23/3.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.23/3.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.23/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.23/3.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.23/3.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.23/3.69  tff('#skF_2', type, '#skF_2': $i).
% 10.23/3.69  tff('#skF_3', type, '#skF_3': $i).
% 10.23/3.69  tff('#skF_1', type, '#skF_1': $i).
% 10.23/3.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.23/3.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.23/3.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.23/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.23/3.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.23/3.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.23/3.69  tff('#skF_4', type, '#skF_4': $i).
% 10.23/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.23/3.69  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.23/3.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.23/3.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.23/3.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.23/3.69  
% 10.45/3.72  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 10.45/3.72  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.45/3.72  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.45/3.72  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.45/3.72  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 10.45/3.72  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.45/3.72  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 10.45/3.72  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.45/3.72  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.45/3.72  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 10.45/3.72  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.45/3.72  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.45/3.72  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.45/3.72  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.45/3.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.45/3.72  tff(c_70, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_1061, plain, (![C_177, A_178, B_179]: (v1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.45/3.72  tff(c_1074, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1061])).
% 10.45/3.72  tff(c_68, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_84, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_68])).
% 10.45/3.72  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_10786, plain, (![A_930, B_931, C_932]: (k1_relset_1(A_930, B_931, C_932)=k1_relat_1(C_932) | ~m1_subset_1(C_932, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.45/3.72  tff(c_10805, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_10786])).
% 10.45/3.72  tff(c_11545, plain, (![B_1020, A_1021, C_1022]: (k1_xboole_0=B_1020 | k1_relset_1(A_1021, B_1020, C_1022)=A_1021 | ~v1_funct_2(C_1022, A_1021, B_1020) | ~m1_subset_1(C_1022, k1_zfmisc_1(k2_zfmisc_1(A_1021, B_1020))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.45/3.72  tff(c_11558, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_11545])).
% 10.45/3.72  tff(c_11572, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10805, c_11558])).
% 10.45/3.72  tff(c_11573, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_11572])).
% 10.45/3.72  tff(c_32, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.45/3.72  tff(c_11588, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11573, c_32])).
% 10.45/3.72  tff(c_11643, plain, (![A_1025]: (k1_relat_1(k7_relat_1('#skF_4', A_1025))=A_1025 | ~r1_tarski(A_1025, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_11588])).
% 10.45/3.72  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_11411, plain, (![A_1010, B_1011, C_1012, D_1013]: (k2_partfun1(A_1010, B_1011, C_1012, D_1013)=k7_relat_1(C_1012, D_1013) | ~m1_subset_1(C_1012, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))) | ~v1_funct_1(C_1012))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.45/3.72  tff(c_11420, plain, (![D_1013]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1013)=k7_relat_1('#skF_4', D_1013) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_11411])).
% 10.45/3.72  tff(c_11432, plain, (![D_1013]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1013)=k7_relat_1('#skF_4', D_1013))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11420])).
% 10.45/3.72  tff(c_2082, plain, (![A_310, B_311, C_312, D_313]: (k2_partfun1(A_310, B_311, C_312, D_313)=k7_relat_1(C_312, D_313) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~v1_funct_1(C_312))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.45/3.72  tff(c_2089, plain, (![D_313]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_313)=k7_relat_1('#skF_4', D_313) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_2082])).
% 10.45/3.72  tff(c_2098, plain, (![D_313]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_313)=k7_relat_1('#skF_4', D_313))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2089])).
% 10.45/3.72  tff(c_2473, plain, (![A_333, B_334, C_335, D_336]: (m1_subset_1(k2_partfun1(A_333, B_334, C_335, D_336), k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))) | ~v1_funct_1(C_335))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_2501, plain, (![D_313]: (m1_subset_1(k7_relat_1('#skF_4', D_313), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2098, c_2473])).
% 10.45/3.72  tff(c_2521, plain, (![D_337]: (m1_subset_1(k7_relat_1('#skF_4', D_337), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2501])).
% 10.45/3.72  tff(c_36, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.45/3.72  tff(c_2561, plain, (![D_337]: (v5_relat_1(k7_relat_1('#skF_4', D_337), '#skF_2'))), inference(resolution, [status(thm)], [c_2521, c_36])).
% 10.45/3.72  tff(c_34, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.45/3.72  tff(c_2562, plain, (![D_337]: (v1_relat_1(k7_relat_1('#skF_4', D_337)))), inference(resolution, [status(thm)], [c_2521, c_34])).
% 10.45/3.72  tff(c_24, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.45/3.72  tff(c_1890, plain, (![A_287, B_288, C_289, D_290]: (v1_funct_1(k2_partfun1(A_287, B_288, C_289, D_290)) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(C_289))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_1895, plain, (![D_290]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_290)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1890])).
% 10.45/3.72  tff(c_1903, plain, (![D_290]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_290)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1895])).
% 10.45/3.72  tff(c_2099, plain, (![D_290]: (v1_funct_1(k7_relat_1('#skF_4', D_290)))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_1903])).
% 10.45/3.72  tff(c_1610, plain, (![A_250, B_251, C_252]: (k1_relset_1(A_250, B_251, C_252)=k1_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.45/3.72  tff(c_1625, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1610])).
% 10.45/3.72  tff(c_2156, plain, (![B_320, A_321, C_322]: (k1_xboole_0=B_320 | k1_relset_1(A_321, B_320, C_322)=A_321 | ~v1_funct_2(C_322, A_321, B_320) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_321, B_320))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.45/3.72  tff(c_2166, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_2156])).
% 10.45/3.72  tff(c_2177, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1625, c_2166])).
% 10.45/3.72  tff(c_2178, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_2177])).
% 10.45/3.72  tff(c_2193, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2178, c_32])).
% 10.45/3.72  tff(c_2203, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_2193])).
% 10.45/3.72  tff(c_1992, plain, (![B_304, A_305]: (m1_subset_1(B_304, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_304), A_305))) | ~r1_tarski(k2_relat_1(B_304), A_305) | ~v1_funct_1(B_304) | ~v1_relat_1(B_304))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.45/3.72  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.45/3.72  tff(c_5994, plain, (![B_593, A_594]: (r1_tarski(B_593, k2_zfmisc_1(k1_relat_1(B_593), A_594)) | ~r1_tarski(k2_relat_1(B_593), A_594) | ~v1_funct_1(B_593) | ~v1_relat_1(B_593))), inference(resolution, [status(thm)], [c_1992, c_18])).
% 10.45/3.72  tff(c_6058, plain, (![A_17, A_594]: (r1_tarski(k7_relat_1('#skF_4', A_17), k2_zfmisc_1(A_17, A_594)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_17)), A_594) | ~v1_funct_1(k7_relat_1('#skF_4', A_17)) | ~v1_relat_1(k7_relat_1('#skF_4', A_17)) | ~r1_tarski(A_17, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_5994])).
% 10.45/3.72  tff(c_7418, plain, (![A_692, A_693]: (r1_tarski(k7_relat_1('#skF_4', A_692), k2_zfmisc_1(A_692, A_693)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_692)), A_693) | ~r1_tarski(A_692, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2099, c_6058])).
% 10.45/3.72  tff(c_7426, plain, (![A_692, A_9]: (r1_tarski(k7_relat_1('#skF_4', A_692), k2_zfmisc_1(A_692, A_9)) | ~r1_tarski(A_692, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_692), A_9) | ~v1_relat_1(k7_relat_1('#skF_4', A_692)))), inference(resolution, [status(thm)], [c_24, c_7418])).
% 10.45/3.72  tff(c_10179, plain, (![A_858, A_859]: (r1_tarski(k7_relat_1('#skF_4', A_858), k2_zfmisc_1(A_858, A_859)) | ~r1_tarski(A_858, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_858), A_859))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_7426])).
% 10.45/3.72  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.45/3.72  tff(c_1037, plain, (![A_171, B_172, C_173, D_174]: (v1_funct_1(k2_partfun1(A_171, B_172, C_173, D_174)) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_1042, plain, (![D_174]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_174)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1037])).
% 10.45/3.72  tff(c_1050, plain, (![D_174]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_174)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1042])).
% 10.45/3.72  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.45/3.72  tff(c_157, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 10.45/3.72  tff(c_1053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1050, c_157])).
% 10.45/3.72  tff(c_1054, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 10.45/3.72  tff(c_1112, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1054])).
% 10.45/3.72  tff(c_1303, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1112])).
% 10.45/3.72  tff(c_2100, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_1303])).
% 10.45/3.72  tff(c_10194, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_10179, c_2100])).
% 10.45/3.72  tff(c_10232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2561, c_70, c_10194])).
% 10.45/3.72  tff(c_10234, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1054])).
% 10.45/3.72  tff(c_10803, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10234, c_10786])).
% 10.45/3.72  tff(c_11435, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11432, c_11432, c_10803])).
% 10.45/3.72  tff(c_10233, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1054])).
% 10.45/3.72  tff(c_11442, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11432, c_10233])).
% 10.45/3.72  tff(c_11441, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_11432, c_10234])).
% 10.45/3.72  tff(c_48, plain, (![B_29, C_30, A_28]: (k1_xboole_0=B_29 | v1_funct_2(C_30, A_28, B_29) | k1_relset_1(A_28, B_29, C_30)!=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.45/3.72  tff(c_11500, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_11441, c_48])).
% 10.45/3.72  tff(c_11522, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11442, c_84, c_11500])).
% 10.45/3.72  tff(c_11540, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11435, c_11522])).
% 10.45/3.72  tff(c_11652, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11643, c_11540])).
% 10.45/3.72  tff(c_11694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_11652])).
% 10.45/3.72  tff(c_11695, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_68])).
% 10.45/3.72  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.45/3.72  tff(c_11710, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_16])).
% 10.45/3.72  tff(c_11696, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 10.45/3.72  tff(c_11702, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11696])).
% 10.45/3.72  tff(c_11720, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11710, c_11702, c_72])).
% 10.45/3.72  tff(c_11790, plain, (![A_1037, B_1038]: (r1_tarski(A_1037, B_1038) | ~m1_subset_1(A_1037, k1_zfmisc_1(B_1038)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.45/3.72  tff(c_11794, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_11720, c_11790])).
% 10.45/3.72  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.45/3.72  tff(c_11740, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_10])).
% 10.45/3.72  tff(c_11798, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_11794, c_11740])).
% 10.45/3.72  tff(c_11703, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11702, c_74])).
% 10.45/3.72  tff(c_13098, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11703])).
% 10.45/3.72  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.45/3.72  tff(c_11697, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_8])).
% 10.45/3.72  tff(c_13102, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11697])).
% 10.45/3.72  tff(c_13099, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11720])).
% 10.45/3.72  tff(c_13101, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11710])).
% 10.45/3.72  tff(c_14504, plain, (![A_1399, B_1400, C_1401, D_1402]: (m1_subset_1(k2_partfun1(A_1399, B_1400, C_1401, D_1402), k1_zfmisc_1(k2_zfmisc_1(A_1399, B_1400))) | ~m1_subset_1(C_1401, k1_zfmisc_1(k2_zfmisc_1(A_1399, B_1400))) | ~v1_funct_1(C_1401))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_16282, plain, (![A_1565, B_1566, C_1567, D_1568]: (v5_relat_1(k2_partfun1(A_1565, B_1566, C_1567, D_1568), B_1566) | ~m1_subset_1(C_1567, k1_zfmisc_1(k2_zfmisc_1(A_1565, B_1566))) | ~v1_funct_1(C_1567))), inference(resolution, [status(thm)], [c_14504, c_36])).
% 10.45/3.72  tff(c_16297, plain, (![B_1569, C_1570, D_1571]: (v5_relat_1(k2_partfun1('#skF_4', B_1569, C_1570, D_1571), B_1569) | ~m1_subset_1(C_1570, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1570))), inference(superposition, [status(thm), theory('equality')], [c_13101, c_16282])).
% 10.45/3.72  tff(c_15405, plain, (![A_1464, B_1465, C_1466, D_1467]: (v1_relat_1(k2_partfun1(A_1464, B_1465, C_1466, D_1467)) | ~m1_subset_1(C_1466, k1_zfmisc_1(k2_zfmisc_1(A_1464, B_1465))) | ~v1_funct_1(C_1466))), inference(resolution, [status(thm)], [c_14504, c_34])).
% 10.45/3.72  tff(c_15420, plain, (![B_1468, C_1469, D_1470]: (v1_relat_1(k2_partfun1('#skF_4', B_1468, C_1469, D_1470)) | ~m1_subset_1(C_1469, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1469))), inference(superposition, [status(thm), theory('equality')], [c_13101, c_15405])).
% 10.45/3.72  tff(c_15424, plain, (![B_1468, D_1470]: (v1_relat_1(k2_partfun1('#skF_4', B_1468, '#skF_4', D_1470)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13099, c_15420])).
% 10.45/3.72  tff(c_15431, plain, (![B_1468, D_1470]: (v1_relat_1(k2_partfun1('#skF_4', B_1468, '#skF_4', D_1470)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_15424])).
% 10.45/3.72  tff(c_13852, plain, (![A_1312, B_1313, C_1314, D_1315]: (v1_funct_1(k2_partfun1(A_1312, B_1313, C_1314, D_1315)) | ~m1_subset_1(C_1314, k1_zfmisc_1(k2_zfmisc_1(A_1312, B_1313))) | ~v1_funct_1(C_1314))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_14372, plain, (![B_1382, C_1383, D_1384]: (v1_funct_1(k2_partfun1('#skF_4', B_1382, C_1383, D_1384)) | ~m1_subset_1(C_1383, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1383))), inference(superposition, [status(thm), theory('equality')], [c_13101, c_13852])).
% 10.45/3.72  tff(c_14374, plain, (![B_1382, D_1384]: (v1_funct_1(k2_partfun1('#skF_4', B_1382, '#skF_4', D_1384)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13099, c_14372])).
% 10.45/3.72  tff(c_14380, plain, (![B_1382, D_1384]: (v1_funct_1(k2_partfun1('#skF_4', B_1382, '#skF_4', D_1384)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14374])).
% 10.45/3.72  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.45/3.72  tff(c_11721, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_14])).
% 10.45/3.72  tff(c_13097, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11721])).
% 10.45/3.72  tff(c_13992, plain, (![B_1336, A_1337]: (m1_subset_1(B_1336, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1336), A_1337))) | ~r1_tarski(k2_relat_1(B_1336), A_1337) | ~v1_funct_1(B_1336) | ~v1_relat_1(B_1336))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.45/3.72  tff(c_14411, plain, (![B_1395]: (m1_subset_1(B_1395, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_1395), '#skF_4') | ~v1_funct_1(B_1395) | ~v1_relat_1(B_1395))), inference(superposition, [status(thm), theory('equality')], [c_13097, c_13992])).
% 10.45/3.72  tff(c_14422, plain, (![B_1396]: (m1_subset_1(B_1396, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_1396) | ~v5_relat_1(B_1396, '#skF_4') | ~v1_relat_1(B_1396))), inference(resolution, [status(thm)], [c_24, c_14411])).
% 10.45/3.72  tff(c_11807, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11720])).
% 10.45/3.72  tff(c_11805, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11721])).
% 10.45/3.72  tff(c_12743, plain, (![A_1168, B_1169, C_1170, D_1171]: (v1_funct_1(k2_partfun1(A_1168, B_1169, C_1170, D_1171)) | ~m1_subset_1(C_1170, k1_zfmisc_1(k2_zfmisc_1(A_1168, B_1169))) | ~v1_funct_1(C_1170))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.45/3.72  tff(c_13060, plain, (![A_1206, C_1207, D_1208]: (v1_funct_1(k2_partfun1(A_1206, '#skF_4', C_1207, D_1208)) | ~m1_subset_1(C_1207, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1207))), inference(superposition, [status(thm), theory('equality')], [c_11805, c_12743])).
% 10.45/3.72  tff(c_13062, plain, (![A_1206, D_1208]: (v1_funct_1(k2_partfun1(A_1206, '#skF_4', '#skF_4', D_1208)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11807, c_13060])).
% 10.45/3.72  tff(c_13068, plain, (![A_1206, D_1208]: (v1_funct_1(k2_partfun1(A_1206, '#skF_4', '#skF_4', D_1208)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13062])).
% 10.45/3.72  tff(c_11741, plain, (![A_1031]: (A_1031='#skF_1' | ~r1_tarski(A_1031, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11695, c_11695, c_10])).
% 10.45/3.72  tff(c_11757, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_70, c_11741])).
% 10.45/3.72  tff(c_11799, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11757, c_11702, c_11757, c_11757, c_11702, c_11702, c_11757, c_11721, c_11702, c_11702, c_66])).
% 10.45/3.72  tff(c_11800, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_11799])).
% 10.45/3.72  tff(c_11906, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11798, c_11800])).
% 10.45/3.72  tff(c_13090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13068, c_11906])).
% 10.45/3.72  tff(c_13091, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_11799])).
% 10.45/3.72  tff(c_13296, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11798, c_11798, c_11798, c_11798, c_11798, c_11798, c_11798, c_11798, c_13091])).
% 10.45/3.72  tff(c_13297, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13296])).
% 10.45/3.72  tff(c_14437, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_14422, c_13297])).
% 10.45/3.72  tff(c_14452, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14380, c_14437])).
% 10.45/3.72  tff(c_14859, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14452])).
% 10.45/3.72  tff(c_15435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15431, c_14859])).
% 10.45/3.72  tff(c_15436, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_14452])).
% 10.45/3.72  tff(c_16306, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16297, c_15436])).
% 10.45/3.72  tff(c_16337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_13099, c_16306])).
% 10.45/3.72  tff(c_16339, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13296])).
% 10.45/3.72  tff(c_16347, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_16339, c_18])).
% 10.45/3.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.45/3.72  tff(c_16352, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_16347, c_2])).
% 10.45/3.72  tff(c_16360, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13102, c_16352])).
% 10.45/3.72  tff(c_16338, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_13296])).
% 10.45/3.72  tff(c_16365, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16360, c_16338])).
% 10.45/3.72  tff(c_16372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13098, c_16365])).
% 10.45/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/3.72  
% 10.45/3.72  Inference rules
% 10.45/3.72  ----------------------
% 10.45/3.72  #Ref     : 0
% 10.45/3.72  #Sup     : 3423
% 10.45/3.72  #Fact    : 0
% 10.45/3.72  #Define  : 0
% 10.45/3.72  #Split   : 27
% 10.45/3.72  #Chain   : 0
% 10.45/3.72  #Close   : 0
% 10.45/3.72  
% 10.45/3.72  Ordering : KBO
% 10.45/3.72  
% 10.45/3.72  Simplification rules
% 10.45/3.72  ----------------------
% 10.45/3.72  #Subsume      : 360
% 10.45/3.72  #Demod        : 5799
% 10.45/3.72  #Tautology    : 1722
% 10.45/3.72  #SimpNegUnit  : 33
% 10.45/3.72  #BackRed      : 78
% 10.45/3.72  
% 10.45/3.72  #Partial instantiations: 0
% 10.45/3.72  #Strategies tried      : 1
% 10.45/3.72  
% 10.45/3.72  Timing (in seconds)
% 10.45/3.72  ----------------------
% 10.45/3.72  Preprocessing        : 0.36
% 10.45/3.72  Parsing              : 0.20
% 10.45/3.72  CNF conversion       : 0.02
% 10.45/3.72  Main loop            : 2.52
% 10.45/3.72  Inferencing          : 0.79
% 10.45/3.72  Reduction            : 1.02
% 10.45/3.72  Demodulation         : 0.77
% 10.45/3.72  BG Simplification    : 0.07
% 10.45/3.72  Subsumption          : 0.47
% 10.45/3.72  Abstraction          : 0.09
% 10.45/3.72  MUC search           : 0.00
% 10.45/3.72  Cooper               : 0.00
% 10.45/3.72  Total                : 2.93
% 10.45/3.72  Index Insertion      : 0.00
% 10.45/3.72  Index Deletion       : 0.00
% 10.45/3.72  Index Matching       : 0.00
% 10.45/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
