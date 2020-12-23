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
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 10.50s
% Output     : CNFRefutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :  245 (4060 expanded)
%              Number of leaves         :   40 (1292 expanded)
%              Depth                    :   21
%              Number of atoms          :  441 (12452 expanded)
%              Number of equality atoms :   96 (4450 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_160,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_28,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_144,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_144])).

tff(c_154,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_150])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_13071,plain,(
    ! [A_740,B_741,C_742] :
      ( k1_relset_1(A_740,B_741,C_742) = k1_relat_1(C_742)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13090,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_13071])).

tff(c_14453,plain,(
    ! [B_836,A_837,C_838] :
      ( k1_xboole_0 = B_836
      | k1_relset_1(A_837,B_836,C_838) = A_837
      | ~ v1_funct_2(C_838,A_837,B_836)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_837,B_836))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14466,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_14453])).

tff(c_14481,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13090,c_14466])).

tff(c_14482,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_14481])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k1_relat_1(k7_relat_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14506,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14482,c_34])).

tff(c_14533,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_14506])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_14240,plain,(
    ! [A_823,B_824,C_825,D_826] :
      ( k2_partfun1(A_823,B_824,C_825,D_826) = k7_relat_1(C_825,D_826)
      | ~ m1_subset_1(C_825,k1_zfmisc_1(k2_zfmisc_1(A_823,B_824)))
      | ~ v1_funct_1(C_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_14247,plain,(
    ! [D_826] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_826) = k7_relat_1('#skF_4',D_826)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_14240])).

tff(c_14258,plain,(
    ! [D_826] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_826) = k7_relat_1('#skF_4',D_826) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14247])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k7_relat_1(B_22,A_21),B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_135,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_135])).

tff(c_2453,plain,(
    ! [A_267,C_268,B_269] :
      ( r1_tarski(A_267,C_268)
      | ~ r1_tarski(B_269,C_268)
      | ~ r1_tarski(A_267,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2542,plain,(
    ! [A_274] :
      ( r1_tarski(A_274,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_274,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_2453])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(A_7)
      | ~ v1_relat_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_2557,plain,(
    ! [A_274] :
      ( v1_relat_1(A_274)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_274,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2542,c_151])).

tff(c_2600,plain,(
    ! [A_276] :
      ( v1_relat_1(A_276)
      | ~ r1_tarski(A_276,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2557])).

tff(c_2615,plain,(
    ! [A_21] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_21))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_2600])).

tff(c_2623,plain,(
    ! [A_21] : v1_relat_1(k7_relat_1('#skF_4',A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2615])).

tff(c_2289,plain,(
    ! [C_231,A_232,B_233] :
      ( v4_relat_1(C_231,A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2303,plain,(
    ! [A_7,A_232,B_233] :
      ( v4_relat_1(A_7,A_232)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_232,B_233)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2289])).

tff(c_2628,plain,(
    ! [A_278] :
      ( v4_relat_1(A_278,'#skF_1')
      | ~ r1_tarski(A_278,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2542,c_2303])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2753,plain,(
    ! [A_291] :
      ( k7_relat_1(A_291,'#skF_1') = A_291
      | ~ v1_relat_1(A_291)
      | ~ r1_tarski(A_291,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2628,c_30])).

tff(c_2768,plain,(
    ! [A_21] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_21),'#skF_1') = k7_relat_1('#skF_4',A_21)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_21))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_2753])).

tff(c_2779,plain,(
    ! [A_292] : k7_relat_1(k7_relat_1('#skF_4',A_292),'#skF_1') = k7_relat_1('#skF_4',A_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2623,c_2768])).

tff(c_2791,plain,(
    ! [A_292] :
      ( r1_tarski(k7_relat_1('#skF_4',A_292),k7_relat_1('#skF_4',A_292))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2779,c_32])).

tff(c_2804,plain,(
    ! [A_292] : r1_tarski(k7_relat_1('#skF_4',A_292),k7_relat_1('#skF_4',A_292)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_2791])).

tff(c_3406,plain,(
    ! [A_320,B_321,A_322] :
      ( r1_tarski(A_320,B_321)
      | ~ r1_tarski(A_320,k7_relat_1(B_321,A_322))
      | ~ v1_relat_1(B_321) ) ),
    inference(resolution,[status(thm)],[c_32,c_2453])).

tff(c_3419,plain,(
    ! [A_292] :
      ( r1_tarski(k7_relat_1('#skF_4',A_292),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2804,c_3406])).

tff(c_3448,plain,(
    ! [A_292] : r1_tarski(k7_relat_1('#skF_4',A_292),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_3419])).

tff(c_2304,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2289])).

tff(c_3488,plain,(
    ! [A_324,B_325,C_326] :
      ( k1_relset_1(A_324,B_325,C_326) = k1_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3503,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3488])).

tff(c_4976,plain,(
    ! [B_435,A_436,C_437] :
      ( k1_xboole_0 = B_435
      | k1_relset_1(A_436,B_435,C_437) = A_436
      | ~ v1_funct_2(C_437,A_436,B_435)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_436,B_435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4986,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4976])).

tff(c_4999,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3503,c_4986])).

tff(c_5000,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4999])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5040,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_1',A_12)
      | ~ v4_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5000,c_20])).

tff(c_5191,plain,(
    ! [A_441] :
      ( r1_tarski('#skF_1',A_441)
      | ~ v4_relat_1('#skF_4',A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_5040])).

tff(c_5219,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2304,c_5191])).

tff(c_4732,plain,(
    ! [D_419,B_420,C_421,A_422] :
      ( m1_subset_1(D_419,k1_zfmisc_1(k2_zfmisc_1(B_420,C_421)))
      | ~ r1_tarski(k1_relat_1(D_419),B_420)
      | ~ m1_subset_1(D_419,k1_zfmisc_1(k2_zfmisc_1(A_422,C_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4794,plain,(
    ! [B_425] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_425,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_425) ) ),
    inference(resolution,[status(thm)],[c_70,c_4732])).

tff(c_38,plain,(
    ! [C_27,A_25,B_26] :
      ( v4_relat_1(C_27,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4825,plain,(
    ! [B_425] :
      ( v4_relat_1('#skF_4',B_425)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_425) ) ),
    inference(resolution,[status(thm)],[c_4794,c_38])).

tff(c_5004,plain,(
    ! [B_425] :
      ( v4_relat_1('#skF_4',B_425)
      | ~ r1_tarski('#skF_1',B_425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5000,c_4825])).

tff(c_2476,plain,(
    ! [B_271,A_272] :
      ( r1_tarski(k1_relat_1(B_271),A_272)
      | ~ v4_relat_1(B_271,A_272)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5643,plain,(
    ! [A_462,A_463,B_464] :
      ( r1_tarski(A_462,A_463)
      | ~ r1_tarski(A_462,k1_relat_1(B_464))
      | ~ v4_relat_1(B_464,A_463)
      | ~ v1_relat_1(B_464) ) ),
    inference(resolution,[status(thm)],[c_2476,c_2])).

tff(c_5647,plain,(
    ! [A_462,A_463] :
      ( r1_tarski(A_462,A_463)
      | ~ r1_tarski(A_462,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_463)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5000,c_5643])).

tff(c_5679,plain,(
    ! [A_465,A_466] :
      ( r1_tarski(A_465,A_466)
      | ~ r1_tarski(A_465,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_5647])).

tff(c_5706,plain,(
    ! [A_467] :
      ( r1_tarski('#skF_3',A_467)
      | ~ v4_relat_1('#skF_4',A_467) ) ),
    inference(resolution,[status(thm)],[c_68,c_5679])).

tff(c_5725,plain,(
    ! [B_425] :
      ( r1_tarski('#skF_3',B_425)
      | ~ r1_tarski('#skF_1',B_425) ) ),
    inference(resolution,[status(thm)],[c_5004,c_5706])).

tff(c_2401,plain,(
    ! [B_261,A_262] :
      ( k7_relat_1(B_261,A_262) = B_261
      | ~ v4_relat_1(B_261,A_262)
      | ~ v1_relat_1(B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2413,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2304,c_2401])).

tff(c_2421,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2413])).

tff(c_2428,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_32])).

tff(c_2434,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2428])).

tff(c_2561,plain,(
    ! [A_274] :
      ( v4_relat_1(A_274,'#skF_1')
      | ~ r1_tarski(A_274,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2542,c_2303])).

tff(c_2953,plain,(
    ! [C_303,A_304,B_305] :
      ( v4_relat_1(k7_relat_1(C_303,A_304),A_304)
      | ~ v4_relat_1(C_303,B_305)
      | ~ v1_relat_1(C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2970,plain,(
    ! [A_274,A_304] :
      ( v4_relat_1(k7_relat_1(A_274,A_304),A_304)
      | ~ v1_relat_1(A_274)
      | ~ r1_tarski(A_274,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2561,c_2953])).

tff(c_5022,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5000,c_34])).

tff(c_5327,plain,(
    ! [A_448] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_448)) = A_448
      | ~ r1_tarski(A_448,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_5022])).

tff(c_5376,plain,(
    ! [A_448,A_12] :
      ( r1_tarski(A_448,A_12)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_448),A_12)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_448))
      | ~ r1_tarski(A_448,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5327,c_20])).

tff(c_6730,plain,(
    ! [A_534,A_535] :
      ( r1_tarski(A_534,A_535)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_534),A_535)
      | ~ r1_tarski(A_534,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_5376])).

tff(c_6749,plain,(
    ! [A_304] :
      ( r1_tarski(A_304,A_304)
      | ~ r1_tarski(A_304,'#skF_1')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2970,c_6730])).

tff(c_6808,plain,(
    ! [A_536] :
      ( r1_tarski(A_536,A_536)
      | ~ r1_tarski(A_536,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_154,c_6749])).

tff(c_6811,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5725,c_6808])).

tff(c_6832,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5219,c_6811])).

tff(c_2967,plain,(
    ! [A_304] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_304),A_304)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2304,c_2953])).

tff(c_2979,plain,(
    ! [A_306] : v4_relat_1(k7_relat_1('#skF_4',A_306),A_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2967])).

tff(c_2995,plain,(
    ! [A_306] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_306),A_306) = k7_relat_1('#skF_4',A_306)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_306)) ) ),
    inference(resolution,[status(thm)],[c_2979,c_30])).

tff(c_3013,plain,(
    ! [A_306] : k7_relat_1(k7_relat_1('#skF_4',A_306),A_306) = k7_relat_1('#skF_4',A_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_2995])).

tff(c_5056,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_5022])).

tff(c_2778,plain,(
    ! [A_21] : k7_relat_1(k7_relat_1('#skF_4',A_21),'#skF_1') = k7_relat_1('#skF_4',A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2623,c_2768])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(k7_relat_1(C_16,A_14),A_14)
      | ~ v4_relat_1(C_16,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2981,plain,(
    ! [A_306,A_14] :
      ( v4_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_306),A_14),A_14)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_306)) ) ),
    inference(resolution,[status(thm)],[c_2979,c_24])).

tff(c_3133,plain,(
    ! [A_310,A_311] : v4_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_310),A_311),A_311) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_2981])).

tff(c_3152,plain,(
    ! [A_21] : v4_relat_1(k7_relat_1('#skF_4',A_21),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_3133])).

tff(c_6874,plain,(
    ! [B_540] :
      ( r1_tarski(k1_relat_1(B_540),k1_relat_1(B_540))
      | ~ v4_relat_1(B_540,'#skF_1')
      | ~ v1_relat_1(B_540) ) ),
    inference(resolution,[status(thm)],[c_20,c_6808])).

tff(c_6900,plain,(
    ! [A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_23)),A_23)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_23),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5056,c_6874])).

tff(c_7033,plain,(
    ! [A_542] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_542)),A_542)
      | ~ r1_tarski(A_542,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_3152,c_6900])).

tff(c_2468,plain,(
    ! [A_267] :
      ( r1_tarski(A_267,'#skF_1')
      | ~ r1_tarski(A_267,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_2453])).

tff(c_7116,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_1')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_7033,c_2468])).

tff(c_7193,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7116])).

tff(c_6790,plain,(
    ! [A_304] :
      ( r1_tarski(A_304,A_304)
      | ~ r1_tarski(A_304,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_154,c_6749])).

tff(c_7231,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7193,c_6790])).

tff(c_7638,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5056,c_7231])).

tff(c_7661,plain,(
    r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7638])).

tff(c_7676,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_7661,c_34])).

tff(c_7698,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2623,c_3013,c_7676])).

tff(c_2465,plain,(
    ! [A_267] :
      ( r1_tarski(A_267,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_267,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_2453])).

tff(c_11428,plain,(
    ! [A_626,B_627,C_628,A_629] :
      ( m1_subset_1(A_626,k1_zfmisc_1(k2_zfmisc_1(B_627,C_628)))
      | ~ r1_tarski(k1_relat_1(A_626),B_627)
      | ~ r1_tarski(A_626,k2_zfmisc_1(A_629,C_628)) ) ),
    inference(resolution,[status(thm)],[c_14,c_4732])).

tff(c_12110,plain,(
    ! [A_658,B_659] :
      ( m1_subset_1(A_658,k1_zfmisc_1(k2_zfmisc_1(B_659,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(A_658),B_659)
      | ~ r1_tarski(A_658,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2465,c_11428])).

tff(c_4863,plain,(
    ! [A_427,B_428,C_429,D_430] :
      ( k2_partfun1(A_427,B_428,C_429,D_430) = k7_relat_1(C_429,D_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428)))
      | ~ v1_funct_1(C_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4870,plain,(
    ! [D_430] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_430) = k7_relat_1('#skF_4',D_430)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_4863])).

tff(c_4881,plain,(
    ! [D_430] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_430) = k7_relat_1('#skF_4',D_430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4870])).

tff(c_2230,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( v1_funct_1(k2_partfun1(A_221,B_222,C_223,D_224))
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2235,plain,(
    ! [D_224] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_224))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_2230])).

tff(c_2243,plain,(
    ! [D_224] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_224)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2235])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_155,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2243,c_155])).

tff(c_2247,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2249,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2247])).

tff(c_4896,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4881,c_2249])).

tff(c_12129,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12110,c_4896])).

tff(c_12172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3448,c_6832,c_7698,c_12129])).

tff(c_12174,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2247])).

tff(c_13088,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12174,c_13071])).

tff(c_14261,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14258,c_14258,c_13088])).

tff(c_12173,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2247])).

tff(c_14269,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14258,c_12173])).

tff(c_14268,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14258,c_12174])).

tff(c_14704,plain,(
    ! [B_843,C_844,A_845] :
      ( k1_xboole_0 = B_843
      | v1_funct_2(C_844,A_845,B_843)
      | k1_relset_1(A_845,B_843,C_844) != A_845
      | ~ m1_subset_1(C_844,k1_zfmisc_1(k2_zfmisc_1(A_845,B_843))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14710,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_14268,c_14704])).

tff(c_14729,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14269,c_86,c_14710])).

tff(c_15004,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14261,c_14729])).

tff(c_15011,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14533,c_15004])).

tff(c_15015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_15011])).

tff(c_15016,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15030,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15016,c_10])).

tff(c_15017,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_15023,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15017])).

tff(c_15040,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15030,c_15023,c_70])).

tff(c_15096,plain,(
    ! [A_869,B_870] :
      ( r1_tarski(A_869,B_870)
      | ~ m1_subset_1(A_869,k1_zfmisc_1(B_870)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15104,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_15040,c_15096])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15059,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15016,c_4])).

tff(c_15108,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15104,c_15059])).

tff(c_15024,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_72])).

tff(c_16217,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15024])).

tff(c_16216,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15040])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15018,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15016,c_8])).

tff(c_16215,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15018])).

tff(c_16391,plain,(
    ! [C_1037,A_1038,B_1039] :
      ( v4_relat_1(C_1037,A_1038)
      | ~ m1_subset_1(C_1037,k1_zfmisc_1(k2_zfmisc_1(A_1038,B_1039))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16495,plain,(
    ! [C_1049,A_1050] :
      ( v4_relat_1(C_1049,A_1050)
      | ~ m1_subset_1(C_1049,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16215,c_16391])).

tff(c_16501,plain,(
    ! [A_1050] : v4_relat_1('#skF_4',A_1050) ),
    inference(resolution,[status(thm)],[c_16216,c_16495])).

tff(c_15031,plain,(
    ! [B_861] : k2_zfmisc_1('#skF_1',B_861) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15016,c_10])).

tff(c_15035,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15031,c_28])).

tff(c_16218,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15035])).

tff(c_16219,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15030])).

tff(c_16404,plain,(
    ! [C_1042] :
      ( v4_relat_1(C_1042,'#skF_4')
      | ~ m1_subset_1(C_1042,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16219,c_16391])).

tff(c_16412,plain,(
    v4_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_16216,c_16404])).

tff(c_16350,plain,(
    ! [B_1024,A_1025] :
      ( r1_tarski(k1_relat_1(B_1024),A_1025)
      | ~ v4_relat_1(B_1024,A_1025)
      | ~ v1_relat_1(B_1024) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16214,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15059])).

tff(c_16362,plain,(
    ! [B_1024] :
      ( k1_relat_1(B_1024) = '#skF_4'
      | ~ v4_relat_1(B_1024,'#skF_4')
      | ~ v1_relat_1(B_1024) ) ),
    inference(resolution,[status(thm)],[c_16350,c_16214])).

tff(c_16419,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16412,c_16362])).

tff(c_16425,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16218,c_16419])).

tff(c_16432,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_4',A_12)
      | ~ v4_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16425,c_20])).

tff(c_16438,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_4',A_12)
      | ~ v4_relat_1('#skF_4',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16218,c_16432])).

tff(c_16505,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16501,c_16438])).

tff(c_15076,plain,(
    ! [B_866,A_867] :
      ( r1_tarski(k7_relat_1(B_866,A_867),B_866)
      | ~ v1_relat_1(B_866) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15080,plain,(
    ! [A_867] :
      ( k7_relat_1('#skF_1',A_867) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_15076,c_15059])).

tff(c_15083,plain,(
    ! [A_867] : k7_relat_1('#skF_1',A_867) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15035,c_15080])).

tff(c_16211,plain,(
    ! [A_867] : k7_relat_1('#skF_4',A_867) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15083])).

tff(c_18071,plain,(
    ! [A_1185,B_1186,C_1187,D_1188] :
      ( m1_subset_1(A_1185,k1_zfmisc_1(k2_zfmisc_1(B_1186,C_1187)))
      | ~ r1_tarski(A_1185,D_1188)
      | ~ m1_subset_1(D_1188,k1_zfmisc_1(k2_zfmisc_1(B_1186,C_1187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18087,plain,(
    ! [B_1189,C_1190,A_1191] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1189,C_1190)))
      | ~ m1_subset_1(A_1191,k1_zfmisc_1(k2_zfmisc_1(B_1189,C_1190))) ) ),
    inference(resolution,[status(thm)],[c_16505,c_18071])).

tff(c_18098,plain,(
    ! [B_1192,C_1193,A_1194] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1192,C_1193)))
      | ~ r1_tarski(A_1194,k2_zfmisc_1(B_1192,C_1193)) ) ),
    inference(resolution,[status(thm)],[c_14,c_18087])).

tff(c_18117,plain,(
    ! [B_1192,C_1193] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_1192,C_1193))) ),
    inference(resolution,[status(thm)],[c_16505,c_18098])).

tff(c_18302,plain,(
    ! [A_1207,B_1208,C_1209,D_1210] :
      ( k2_partfun1(A_1207,B_1208,C_1209,D_1210) = k7_relat_1(C_1209,D_1210)
      | ~ m1_subset_1(C_1209,k1_zfmisc_1(k2_zfmisc_1(A_1207,B_1208)))
      | ~ v1_funct_1(C_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18304,plain,(
    ! [B_1192,C_1193,D_1210] :
      ( k2_partfun1(B_1192,C_1193,'#skF_4',D_1210) = k7_relat_1('#skF_4',D_1210)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18117,c_18302])).

tff(c_18314,plain,(
    ! [B_1192,C_1193,D_1210] : k2_partfun1(B_1192,C_1193,'#skF_4',D_1210) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16211,c_18304])).

tff(c_15117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15040])).

tff(c_15116,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15018])).

tff(c_15894,plain,(
    ! [A_969,B_970,C_971,D_972] :
      ( v1_funct_1(k2_partfun1(A_969,B_970,C_971,D_972))
      | ~ m1_subset_1(C_971,k1_zfmisc_1(k2_zfmisc_1(A_969,B_970)))
      | ~ v1_funct_1(C_971) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16194,plain,(
    ! [A_1006,C_1007,D_1008] :
      ( v1_funct_1(k2_partfun1(A_1006,'#skF_4',C_1007,D_1008))
      | ~ m1_subset_1(C_1007,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1007) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15116,c_15894])).

tff(c_16196,plain,(
    ! [A_1006,D_1008] :
      ( v1_funct_1(k2_partfun1(A_1006,'#skF_4','#skF_4',D_1008))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15117,c_16194])).

tff(c_16202,plain,(
    ! [A_1006,D_1008] : v1_funct_1(k2_partfun1(A_1006,'#skF_4','#skF_4',D_1008)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16196])).

tff(c_15060,plain,(
    ! [A_863] :
      ( A_863 = '#skF_1'
      | ~ r1_tarski(A_863,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15016,c_15016,c_4])).

tff(c_15064,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_15060])).

tff(c_15109,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15064,c_15023,c_15064,c_15064,c_15023,c_15023,c_15064,c_15018,c_15023,c_15023,c_64])).

tff(c_15110,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15109])).

tff(c_15209,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15108,c_15110])).

tff(c_16206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16202,c_15209])).

tff(c_16207,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15109])).

tff(c_16344,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_15108,c_15108,c_15108,c_15108,c_15108,c_15108,c_15108,c_15108,c_16207])).

tff(c_16345,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16344])).

tff(c_16349,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_16345])).

tff(c_18317,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18314,c_16349])).

tff(c_18322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16505,c_18317])).

tff(c_18324,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16344])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18334,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18324,c_12])).

tff(c_18347,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18334,c_16214])).

tff(c_18323,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16344])).

tff(c_18352,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18347,c_18323])).

tff(c_18359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16217,c_18352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.50/3.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.78  
% 10.74/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.74/3.78  
% 10.74/3.78  %Foreground sorts:
% 10.74/3.78  
% 10.74/3.78  
% 10.74/3.78  %Background operators:
% 10.74/3.78  
% 10.74/3.78  
% 10.74/3.78  %Foreground operators:
% 10.74/3.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.74/3.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/3.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.74/3.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.74/3.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/3.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.74/3.78  tff('#skF_2', type, '#skF_2': $i).
% 10.74/3.78  tff('#skF_3', type, '#skF_3': $i).
% 10.74/3.78  tff('#skF_1', type, '#skF_1': $i).
% 10.74/3.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.74/3.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.74/3.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.74/3.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/3.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.74/3.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.74/3.78  tff('#skF_4', type, '#skF_4': $i).
% 10.74/3.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/3.78  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.74/3.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.74/3.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.74/3.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.74/3.78  
% 10.74/3.81  tff(f_160, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 10.74/3.81  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.74/3.81  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.74/3.81  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.74/3.81  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.74/3.81  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 10.74/3.81  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.74/3.81  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 10.74/3.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.74/3.81  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.74/3.81  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.74/3.81  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.74/3.81  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.74/3.81  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 10.74/3.81  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 10.74/3.81  tff(f_134, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 10.74/3.81  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.74/3.81  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.74/3.81  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 10.74/3.81  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_28, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.74/3.81  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_144, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.74/3.81  tff(c_150, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_144])).
% 10.74/3.81  tff(c_154, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_150])).
% 10.74/3.81  tff(c_66, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_86, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 10.74/3.81  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_13071, plain, (![A_740, B_741, C_742]: (k1_relset_1(A_740, B_741, C_742)=k1_relat_1(C_742) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.74/3.81  tff(c_13090, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_13071])).
% 10.74/3.81  tff(c_14453, plain, (![B_836, A_837, C_838]: (k1_xboole_0=B_836 | k1_relset_1(A_837, B_836, C_838)=A_837 | ~v1_funct_2(C_838, A_837, B_836) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(A_837, B_836))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.74/3.81  tff(c_14466, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_14453])).
% 10.74/3.81  tff(c_14481, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13090, c_14466])).
% 10.74/3.81  tff(c_14482, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_14481])).
% 10.74/3.81  tff(c_34, plain, (![B_24, A_23]: (k1_relat_1(k7_relat_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.74/3.81  tff(c_14506, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14482, c_34])).
% 10.74/3.81  tff(c_14533, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_14506])).
% 10.74/3.81  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_14240, plain, (![A_823, B_824, C_825, D_826]: (k2_partfun1(A_823, B_824, C_825, D_826)=k7_relat_1(C_825, D_826) | ~m1_subset_1(C_825, k1_zfmisc_1(k2_zfmisc_1(A_823, B_824))) | ~v1_funct_1(C_825))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.74/3.81  tff(c_14247, plain, (![D_826]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_826)=k7_relat_1('#skF_4', D_826) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_14240])).
% 10.74/3.81  tff(c_14258, plain, (![D_826]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_826)=k7_relat_1('#skF_4', D_826))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14247])).
% 10.74/3.81  tff(c_32, plain, (![B_22, A_21]: (r1_tarski(k7_relat_1(B_22, A_21), B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.81  tff(c_135, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.81  tff(c_143, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_135])).
% 10.74/3.81  tff(c_2453, plain, (![A_267, C_268, B_269]: (r1_tarski(A_267, C_268) | ~r1_tarski(B_269, C_268) | ~r1_tarski(A_267, B_269))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.74/3.81  tff(c_2542, plain, (![A_274]: (r1_tarski(A_274, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_274, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_2453])).
% 10.74/3.81  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.81  tff(c_151, plain, (![A_7, B_8]: (v1_relat_1(A_7) | ~v1_relat_1(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_144])).
% 10.74/3.81  tff(c_2557, plain, (![A_274]: (v1_relat_1(A_274) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_274, '#skF_4'))), inference(resolution, [status(thm)], [c_2542, c_151])).
% 10.74/3.81  tff(c_2600, plain, (![A_276]: (v1_relat_1(A_276) | ~r1_tarski(A_276, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2557])).
% 10.74/3.81  tff(c_2615, plain, (![A_21]: (v1_relat_1(k7_relat_1('#skF_4', A_21)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_2600])).
% 10.74/3.81  tff(c_2623, plain, (![A_21]: (v1_relat_1(k7_relat_1('#skF_4', A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2615])).
% 10.74/3.81  tff(c_2289, plain, (![C_231, A_232, B_233]: (v4_relat_1(C_231, A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.74/3.81  tff(c_2303, plain, (![A_7, A_232, B_233]: (v4_relat_1(A_7, A_232) | ~r1_tarski(A_7, k2_zfmisc_1(A_232, B_233)))), inference(resolution, [status(thm)], [c_14, c_2289])).
% 10.74/3.81  tff(c_2628, plain, (![A_278]: (v4_relat_1(A_278, '#skF_1') | ~r1_tarski(A_278, '#skF_4'))), inference(resolution, [status(thm)], [c_2542, c_2303])).
% 10.74/3.81  tff(c_30, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.74/3.81  tff(c_2753, plain, (![A_291]: (k7_relat_1(A_291, '#skF_1')=A_291 | ~v1_relat_1(A_291) | ~r1_tarski(A_291, '#skF_4'))), inference(resolution, [status(thm)], [c_2628, c_30])).
% 10.74/3.81  tff(c_2768, plain, (![A_21]: (k7_relat_1(k7_relat_1('#skF_4', A_21), '#skF_1')=k7_relat_1('#skF_4', A_21) | ~v1_relat_1(k7_relat_1('#skF_4', A_21)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_2753])).
% 10.74/3.81  tff(c_2779, plain, (![A_292]: (k7_relat_1(k7_relat_1('#skF_4', A_292), '#skF_1')=k7_relat_1('#skF_4', A_292))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2623, c_2768])).
% 10.74/3.81  tff(c_2791, plain, (![A_292]: (r1_tarski(k7_relat_1('#skF_4', A_292), k7_relat_1('#skF_4', A_292)) | ~v1_relat_1(k7_relat_1('#skF_4', A_292)))), inference(superposition, [status(thm), theory('equality')], [c_2779, c_32])).
% 10.74/3.81  tff(c_2804, plain, (![A_292]: (r1_tarski(k7_relat_1('#skF_4', A_292), k7_relat_1('#skF_4', A_292)))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_2791])).
% 10.74/3.81  tff(c_3406, plain, (![A_320, B_321, A_322]: (r1_tarski(A_320, B_321) | ~r1_tarski(A_320, k7_relat_1(B_321, A_322)) | ~v1_relat_1(B_321))), inference(resolution, [status(thm)], [c_32, c_2453])).
% 10.74/3.81  tff(c_3419, plain, (![A_292]: (r1_tarski(k7_relat_1('#skF_4', A_292), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2804, c_3406])).
% 10.74/3.81  tff(c_3448, plain, (![A_292]: (r1_tarski(k7_relat_1('#skF_4', A_292), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_3419])).
% 10.74/3.81  tff(c_2304, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_2289])).
% 10.74/3.81  tff(c_3488, plain, (![A_324, B_325, C_326]: (k1_relset_1(A_324, B_325, C_326)=k1_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.74/3.81  tff(c_3503, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3488])).
% 10.74/3.81  tff(c_4976, plain, (![B_435, A_436, C_437]: (k1_xboole_0=B_435 | k1_relset_1(A_436, B_435, C_437)=A_436 | ~v1_funct_2(C_437, A_436, B_435) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_436, B_435))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.74/3.81  tff(c_4986, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4976])).
% 10.74/3.81  tff(c_4999, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3503, c_4986])).
% 10.74/3.81  tff(c_5000, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_4999])).
% 10.74/3.81  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.74/3.81  tff(c_5040, plain, (![A_12]: (r1_tarski('#skF_1', A_12) | ~v4_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5000, c_20])).
% 10.74/3.81  tff(c_5191, plain, (![A_441]: (r1_tarski('#skF_1', A_441) | ~v4_relat_1('#skF_4', A_441))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_5040])).
% 10.74/3.81  tff(c_5219, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2304, c_5191])).
% 10.74/3.81  tff(c_4732, plain, (![D_419, B_420, C_421, A_422]: (m1_subset_1(D_419, k1_zfmisc_1(k2_zfmisc_1(B_420, C_421))) | ~r1_tarski(k1_relat_1(D_419), B_420) | ~m1_subset_1(D_419, k1_zfmisc_1(k2_zfmisc_1(A_422, C_421))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.74/3.81  tff(c_4794, plain, (![B_425]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_425, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_425))), inference(resolution, [status(thm)], [c_70, c_4732])).
% 10.74/3.81  tff(c_38, plain, (![C_27, A_25, B_26]: (v4_relat_1(C_27, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.74/3.81  tff(c_4825, plain, (![B_425]: (v4_relat_1('#skF_4', B_425) | ~r1_tarski(k1_relat_1('#skF_4'), B_425))), inference(resolution, [status(thm)], [c_4794, c_38])).
% 10.74/3.81  tff(c_5004, plain, (![B_425]: (v4_relat_1('#skF_4', B_425) | ~r1_tarski('#skF_1', B_425))), inference(demodulation, [status(thm), theory('equality')], [c_5000, c_4825])).
% 10.74/3.81  tff(c_2476, plain, (![B_271, A_272]: (r1_tarski(k1_relat_1(B_271), A_272) | ~v4_relat_1(B_271, A_272) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.74/3.81  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.74/3.81  tff(c_5643, plain, (![A_462, A_463, B_464]: (r1_tarski(A_462, A_463) | ~r1_tarski(A_462, k1_relat_1(B_464)) | ~v4_relat_1(B_464, A_463) | ~v1_relat_1(B_464))), inference(resolution, [status(thm)], [c_2476, c_2])).
% 10.74/3.81  tff(c_5647, plain, (![A_462, A_463]: (r1_tarski(A_462, A_463) | ~r1_tarski(A_462, '#skF_1') | ~v4_relat_1('#skF_4', A_463) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5000, c_5643])).
% 10.74/3.81  tff(c_5679, plain, (![A_465, A_466]: (r1_tarski(A_465, A_466) | ~r1_tarski(A_465, '#skF_1') | ~v4_relat_1('#skF_4', A_466))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_5647])).
% 10.74/3.81  tff(c_5706, plain, (![A_467]: (r1_tarski('#skF_3', A_467) | ~v4_relat_1('#skF_4', A_467))), inference(resolution, [status(thm)], [c_68, c_5679])).
% 10.74/3.81  tff(c_5725, plain, (![B_425]: (r1_tarski('#skF_3', B_425) | ~r1_tarski('#skF_1', B_425))), inference(resolution, [status(thm)], [c_5004, c_5706])).
% 10.74/3.81  tff(c_2401, plain, (![B_261, A_262]: (k7_relat_1(B_261, A_262)=B_261 | ~v4_relat_1(B_261, A_262) | ~v1_relat_1(B_261))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.74/3.81  tff(c_2413, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2304, c_2401])).
% 10.74/3.81  tff(c_2421, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2413])).
% 10.74/3.81  tff(c_2428, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2421, c_32])).
% 10.74/3.81  tff(c_2434, plain, (r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2428])).
% 10.74/3.81  tff(c_2561, plain, (![A_274]: (v4_relat_1(A_274, '#skF_1') | ~r1_tarski(A_274, '#skF_4'))), inference(resolution, [status(thm)], [c_2542, c_2303])).
% 10.74/3.81  tff(c_2953, plain, (![C_303, A_304, B_305]: (v4_relat_1(k7_relat_1(C_303, A_304), A_304) | ~v4_relat_1(C_303, B_305) | ~v1_relat_1(C_303))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.74/3.81  tff(c_2970, plain, (![A_274, A_304]: (v4_relat_1(k7_relat_1(A_274, A_304), A_304) | ~v1_relat_1(A_274) | ~r1_tarski(A_274, '#skF_4'))), inference(resolution, [status(thm)], [c_2561, c_2953])).
% 10.74/3.81  tff(c_5022, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5000, c_34])).
% 10.74/3.81  tff(c_5327, plain, (![A_448]: (k1_relat_1(k7_relat_1('#skF_4', A_448))=A_448 | ~r1_tarski(A_448, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_5022])).
% 10.74/3.81  tff(c_5376, plain, (![A_448, A_12]: (r1_tarski(A_448, A_12) | ~v4_relat_1(k7_relat_1('#skF_4', A_448), A_12) | ~v1_relat_1(k7_relat_1('#skF_4', A_448)) | ~r1_tarski(A_448, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5327, c_20])).
% 10.74/3.81  tff(c_6730, plain, (![A_534, A_535]: (r1_tarski(A_534, A_535) | ~v4_relat_1(k7_relat_1('#skF_4', A_534), A_535) | ~r1_tarski(A_534, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_5376])).
% 10.74/3.81  tff(c_6749, plain, (![A_304]: (r1_tarski(A_304, A_304) | ~r1_tarski(A_304, '#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2970, c_6730])).
% 10.74/3.81  tff(c_6808, plain, (![A_536]: (r1_tarski(A_536, A_536) | ~r1_tarski(A_536, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2434, c_154, c_6749])).
% 10.74/3.81  tff(c_6811, plain, (r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5725, c_6808])).
% 10.74/3.81  tff(c_6832, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5219, c_6811])).
% 10.74/3.81  tff(c_2967, plain, (![A_304]: (v4_relat_1(k7_relat_1('#skF_4', A_304), A_304) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2304, c_2953])).
% 10.74/3.81  tff(c_2979, plain, (![A_306]: (v4_relat_1(k7_relat_1('#skF_4', A_306), A_306))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2967])).
% 10.74/3.81  tff(c_2995, plain, (![A_306]: (k7_relat_1(k7_relat_1('#skF_4', A_306), A_306)=k7_relat_1('#skF_4', A_306) | ~v1_relat_1(k7_relat_1('#skF_4', A_306)))), inference(resolution, [status(thm)], [c_2979, c_30])).
% 10.74/3.81  tff(c_3013, plain, (![A_306]: (k7_relat_1(k7_relat_1('#skF_4', A_306), A_306)=k7_relat_1('#skF_4', A_306))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_2995])).
% 10.74/3.81  tff(c_5056, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_5022])).
% 10.74/3.81  tff(c_2778, plain, (![A_21]: (k7_relat_1(k7_relat_1('#skF_4', A_21), '#skF_1')=k7_relat_1('#skF_4', A_21))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2623, c_2768])).
% 10.74/3.81  tff(c_24, plain, (![C_16, A_14, B_15]: (v4_relat_1(k7_relat_1(C_16, A_14), A_14) | ~v4_relat_1(C_16, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.74/3.81  tff(c_2981, plain, (![A_306, A_14]: (v4_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_306), A_14), A_14) | ~v1_relat_1(k7_relat_1('#skF_4', A_306)))), inference(resolution, [status(thm)], [c_2979, c_24])).
% 10.74/3.81  tff(c_3133, plain, (![A_310, A_311]: (v4_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_310), A_311), A_311))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_2981])).
% 10.74/3.81  tff(c_3152, plain, (![A_21]: (v4_relat_1(k7_relat_1('#skF_4', A_21), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2778, c_3133])).
% 10.74/3.81  tff(c_6874, plain, (![B_540]: (r1_tarski(k1_relat_1(B_540), k1_relat_1(B_540)) | ~v4_relat_1(B_540, '#skF_1') | ~v1_relat_1(B_540))), inference(resolution, [status(thm)], [c_20, c_6808])).
% 10.74/3.81  tff(c_6900, plain, (![A_23]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_23)), A_23) | ~v4_relat_1(k7_relat_1('#skF_4', A_23), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~r1_tarski(A_23, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5056, c_6874])).
% 10.74/3.81  tff(c_7033, plain, (![A_542]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_542)), A_542) | ~r1_tarski(A_542, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_3152, c_6900])).
% 10.74/3.81  tff(c_2468, plain, (![A_267]: (r1_tarski(A_267, '#skF_1') | ~r1_tarski(A_267, '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_2453])).
% 10.74/3.81  tff(c_7116, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_1') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_7033, c_2468])).
% 10.74/3.81  tff(c_7193, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7116])).
% 10.74/3.81  tff(c_6790, plain, (![A_304]: (r1_tarski(A_304, A_304) | ~r1_tarski(A_304, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2434, c_154, c_6749])).
% 10.74/3.81  tff(c_7231, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_7193, c_6790])).
% 10.74/3.81  tff(c_7638, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5056, c_7231])).
% 10.74/3.81  tff(c_7661, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7638])).
% 10.74/3.81  tff(c_7676, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'))='#skF_3' | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_7661, c_34])).
% 10.74/3.81  tff(c_7698, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2623, c_3013, c_7676])).
% 10.74/3.81  tff(c_2465, plain, (![A_267]: (r1_tarski(A_267, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_267, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_2453])).
% 10.74/3.81  tff(c_11428, plain, (![A_626, B_627, C_628, A_629]: (m1_subset_1(A_626, k1_zfmisc_1(k2_zfmisc_1(B_627, C_628))) | ~r1_tarski(k1_relat_1(A_626), B_627) | ~r1_tarski(A_626, k2_zfmisc_1(A_629, C_628)))), inference(resolution, [status(thm)], [c_14, c_4732])).
% 10.74/3.81  tff(c_12110, plain, (![A_658, B_659]: (m1_subset_1(A_658, k1_zfmisc_1(k2_zfmisc_1(B_659, '#skF_2'))) | ~r1_tarski(k1_relat_1(A_658), B_659) | ~r1_tarski(A_658, '#skF_4'))), inference(resolution, [status(thm)], [c_2465, c_11428])).
% 10.74/3.81  tff(c_4863, plain, (![A_427, B_428, C_429, D_430]: (k2_partfun1(A_427, B_428, C_429, D_430)=k7_relat_1(C_429, D_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))) | ~v1_funct_1(C_429))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.74/3.81  tff(c_4870, plain, (![D_430]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_430)=k7_relat_1('#skF_4', D_430) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_4863])).
% 10.74/3.81  tff(c_4881, plain, (![D_430]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_430)=k7_relat_1('#skF_4', D_430))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4870])).
% 10.74/3.81  tff(c_2230, plain, (![A_221, B_222, C_223, D_224]: (v1_funct_1(k2_partfun1(A_221, B_222, C_223, D_224)) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.74/3.81  tff(c_2235, plain, (![D_224]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_224)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_2230])).
% 10.74/3.81  tff(c_2243, plain, (![D_224]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_224)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2235])).
% 10.74/3.81  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.74/3.81  tff(c_155, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 10.74/3.81  tff(c_2246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2243, c_155])).
% 10.74/3.81  tff(c_2247, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 10.74/3.81  tff(c_2249, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2247])).
% 10.74/3.81  tff(c_4896, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4881, c_2249])).
% 10.74/3.81  tff(c_12129, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_12110, c_4896])).
% 10.74/3.81  tff(c_12172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3448, c_6832, c_7698, c_12129])).
% 10.74/3.81  tff(c_12174, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2247])).
% 10.74/3.81  tff(c_13088, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12174, c_13071])).
% 10.74/3.81  tff(c_14261, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14258, c_14258, c_13088])).
% 10.74/3.81  tff(c_12173, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2247])).
% 10.74/3.81  tff(c_14269, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14258, c_12173])).
% 10.74/3.81  tff(c_14268, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14258, c_12174])).
% 10.74/3.81  tff(c_14704, plain, (![B_843, C_844, A_845]: (k1_xboole_0=B_843 | v1_funct_2(C_844, A_845, B_843) | k1_relset_1(A_845, B_843, C_844)!=A_845 | ~m1_subset_1(C_844, k1_zfmisc_1(k2_zfmisc_1(A_845, B_843))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.74/3.81  tff(c_14710, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_14268, c_14704])).
% 10.74/3.81  tff(c_14729, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14269, c_86, c_14710])).
% 10.74/3.81  tff(c_15004, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14261, c_14729])).
% 10.74/3.81  tff(c_15011, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14533, c_15004])).
% 10.74/3.81  tff(c_15015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_15011])).
% 10.74/3.81  tff(c_15016, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 10.74/3.81  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.74/3.81  tff(c_15030, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15016, c_10])).
% 10.74/3.81  tff(c_15017, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 10.74/3.81  tff(c_15023, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15017])).
% 10.74/3.81  tff(c_15040, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15030, c_15023, c_70])).
% 10.74/3.81  tff(c_15096, plain, (![A_869, B_870]: (r1_tarski(A_869, B_870) | ~m1_subset_1(A_869, k1_zfmisc_1(B_870)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.81  tff(c_15104, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_15040, c_15096])).
% 10.74/3.81  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.74/3.81  tff(c_15059, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15016, c_4])).
% 10.74/3.81  tff(c_15108, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_15104, c_15059])).
% 10.74/3.81  tff(c_15024, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_72])).
% 10.74/3.81  tff(c_16217, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15024])).
% 10.74/3.81  tff(c_16216, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15040])).
% 10.74/3.81  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.74/3.81  tff(c_15018, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15016, c_8])).
% 10.74/3.81  tff(c_16215, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15018])).
% 10.74/3.81  tff(c_16391, plain, (![C_1037, A_1038, B_1039]: (v4_relat_1(C_1037, A_1038) | ~m1_subset_1(C_1037, k1_zfmisc_1(k2_zfmisc_1(A_1038, B_1039))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.74/3.81  tff(c_16495, plain, (![C_1049, A_1050]: (v4_relat_1(C_1049, A_1050) | ~m1_subset_1(C_1049, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_16215, c_16391])).
% 10.74/3.81  tff(c_16501, plain, (![A_1050]: (v4_relat_1('#skF_4', A_1050))), inference(resolution, [status(thm)], [c_16216, c_16495])).
% 10.74/3.81  tff(c_15031, plain, (![B_861]: (k2_zfmisc_1('#skF_1', B_861)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15016, c_10])).
% 10.74/3.81  tff(c_15035, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15031, c_28])).
% 10.74/3.81  tff(c_16218, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15035])).
% 10.74/3.81  tff(c_16219, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15030])).
% 10.74/3.81  tff(c_16404, plain, (![C_1042]: (v4_relat_1(C_1042, '#skF_4') | ~m1_subset_1(C_1042, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_16219, c_16391])).
% 10.74/3.81  tff(c_16412, plain, (v4_relat_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_16216, c_16404])).
% 10.74/3.81  tff(c_16350, plain, (![B_1024, A_1025]: (r1_tarski(k1_relat_1(B_1024), A_1025) | ~v4_relat_1(B_1024, A_1025) | ~v1_relat_1(B_1024))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.74/3.81  tff(c_16214, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15059])).
% 10.74/3.81  tff(c_16362, plain, (![B_1024]: (k1_relat_1(B_1024)='#skF_4' | ~v4_relat_1(B_1024, '#skF_4') | ~v1_relat_1(B_1024))), inference(resolution, [status(thm)], [c_16350, c_16214])).
% 10.74/3.81  tff(c_16419, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16412, c_16362])).
% 10.74/3.81  tff(c_16425, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16218, c_16419])).
% 10.74/3.81  tff(c_16432, plain, (![A_12]: (r1_tarski('#skF_4', A_12) | ~v4_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16425, c_20])).
% 10.74/3.81  tff(c_16438, plain, (![A_12]: (r1_tarski('#skF_4', A_12) | ~v4_relat_1('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_16218, c_16432])).
% 10.74/3.81  tff(c_16505, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_16501, c_16438])).
% 10.74/3.81  tff(c_15076, plain, (![B_866, A_867]: (r1_tarski(k7_relat_1(B_866, A_867), B_866) | ~v1_relat_1(B_866))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.74/3.81  tff(c_15080, plain, (![A_867]: (k7_relat_1('#skF_1', A_867)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_15076, c_15059])).
% 10.74/3.81  tff(c_15083, plain, (![A_867]: (k7_relat_1('#skF_1', A_867)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15035, c_15080])).
% 10.74/3.81  tff(c_16211, plain, (![A_867]: (k7_relat_1('#skF_4', A_867)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15083])).
% 10.74/3.81  tff(c_18071, plain, (![A_1185, B_1186, C_1187, D_1188]: (m1_subset_1(A_1185, k1_zfmisc_1(k2_zfmisc_1(B_1186, C_1187))) | ~r1_tarski(A_1185, D_1188) | ~m1_subset_1(D_1188, k1_zfmisc_1(k2_zfmisc_1(B_1186, C_1187))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.74/3.81  tff(c_18087, plain, (![B_1189, C_1190, A_1191]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1189, C_1190))) | ~m1_subset_1(A_1191, k1_zfmisc_1(k2_zfmisc_1(B_1189, C_1190))))), inference(resolution, [status(thm)], [c_16505, c_18071])).
% 10.74/3.81  tff(c_18098, plain, (![B_1192, C_1193, A_1194]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1192, C_1193))) | ~r1_tarski(A_1194, k2_zfmisc_1(B_1192, C_1193)))), inference(resolution, [status(thm)], [c_14, c_18087])).
% 10.74/3.81  tff(c_18117, plain, (![B_1192, C_1193]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_1192, C_1193))))), inference(resolution, [status(thm)], [c_16505, c_18098])).
% 10.74/3.81  tff(c_18302, plain, (![A_1207, B_1208, C_1209, D_1210]: (k2_partfun1(A_1207, B_1208, C_1209, D_1210)=k7_relat_1(C_1209, D_1210) | ~m1_subset_1(C_1209, k1_zfmisc_1(k2_zfmisc_1(A_1207, B_1208))) | ~v1_funct_1(C_1209))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.74/3.81  tff(c_18304, plain, (![B_1192, C_1193, D_1210]: (k2_partfun1(B_1192, C_1193, '#skF_4', D_1210)=k7_relat_1('#skF_4', D_1210) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18117, c_18302])).
% 10.74/3.81  tff(c_18314, plain, (![B_1192, C_1193, D_1210]: (k2_partfun1(B_1192, C_1193, '#skF_4', D_1210)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16211, c_18304])).
% 10.74/3.81  tff(c_15117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15040])).
% 10.74/3.81  tff(c_15116, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15018])).
% 10.74/3.81  tff(c_15894, plain, (![A_969, B_970, C_971, D_972]: (v1_funct_1(k2_partfun1(A_969, B_970, C_971, D_972)) | ~m1_subset_1(C_971, k1_zfmisc_1(k2_zfmisc_1(A_969, B_970))) | ~v1_funct_1(C_971))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.74/3.81  tff(c_16194, plain, (![A_1006, C_1007, D_1008]: (v1_funct_1(k2_partfun1(A_1006, '#skF_4', C_1007, D_1008)) | ~m1_subset_1(C_1007, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1007))), inference(superposition, [status(thm), theory('equality')], [c_15116, c_15894])).
% 10.74/3.81  tff(c_16196, plain, (![A_1006, D_1008]: (v1_funct_1(k2_partfun1(A_1006, '#skF_4', '#skF_4', D_1008)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_15117, c_16194])).
% 10.74/3.81  tff(c_16202, plain, (![A_1006, D_1008]: (v1_funct_1(k2_partfun1(A_1006, '#skF_4', '#skF_4', D_1008)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16196])).
% 10.74/3.81  tff(c_15060, plain, (![A_863]: (A_863='#skF_1' | ~r1_tarski(A_863, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15016, c_15016, c_4])).
% 10.74/3.81  tff(c_15064, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_68, c_15060])).
% 10.74/3.81  tff(c_15109, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15064, c_15023, c_15064, c_15064, c_15023, c_15023, c_15064, c_15018, c_15023, c_15023, c_64])).
% 10.74/3.81  tff(c_15110, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_15109])).
% 10.74/3.81  tff(c_15209, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15108, c_15110])).
% 10.74/3.81  tff(c_16206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16202, c_15209])).
% 10.74/3.81  tff(c_16207, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_15109])).
% 10.74/3.81  tff(c_16344, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15108, c_15108, c_15108, c_15108, c_15108, c_15108, c_15108, c_15108, c_15108, c_16207])).
% 10.74/3.81  tff(c_16345, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16344])).
% 10.74/3.81  tff(c_16349, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_16345])).
% 10.74/3.81  tff(c_18317, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18314, c_16349])).
% 10.74/3.81  tff(c_18322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16505, c_18317])).
% 10.74/3.81  tff(c_18324, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_16344])).
% 10.74/3.81  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.74/3.81  tff(c_18334, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18324, c_12])).
% 10.74/3.81  tff(c_18347, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_18334, c_16214])).
% 10.74/3.81  tff(c_18323, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_16344])).
% 10.74/3.81  tff(c_18352, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18347, c_18323])).
% 10.74/3.81  tff(c_18359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16217, c_18352])).
% 10.74/3.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.81  
% 10.74/3.81  Inference rules
% 10.74/3.81  ----------------------
% 10.74/3.81  #Ref     : 0
% 10.74/3.81  #Sup     : 3838
% 10.74/3.81  #Fact    : 0
% 10.74/3.81  #Define  : 0
% 10.74/3.81  #Split   : 33
% 10.74/3.81  #Chain   : 0
% 10.74/3.81  #Close   : 0
% 10.74/3.81  
% 10.74/3.81  Ordering : KBO
% 10.74/3.81  
% 10.74/3.81  Simplification rules
% 10.74/3.81  ----------------------
% 10.74/3.81  #Subsume      : 1027
% 10.74/3.81  #Demod        : 3868
% 10.74/3.81  #Tautology    : 1555
% 10.74/3.81  #SimpNegUnit  : 122
% 10.74/3.81  #BackRed      : 89
% 10.74/3.81  
% 10.74/3.81  #Partial instantiations: 0
% 10.74/3.81  #Strategies tried      : 1
% 10.74/3.81  
% 10.74/3.81  Timing (in seconds)
% 10.74/3.81  ----------------------
% 10.74/3.81  Preprocessing        : 0.37
% 10.74/3.81  Parsing              : 0.20
% 10.74/3.81  CNF conversion       : 0.03
% 10.74/3.81  Main loop            : 2.60
% 10.74/3.81  Inferencing          : 0.78
% 10.74/3.81  Reduction            : 1.00
% 10.74/3.81  Demodulation         : 0.74
% 10.74/3.81  BG Simplification    : 0.07
% 10.74/3.81  Subsumption          : 0.54
% 10.74/3.81  Abstraction          : 0.10
% 10.74/3.81  MUC search           : 0.00
% 10.74/3.81  Cooper               : 0.00
% 10.74/3.81  Total                : 3.04
% 10.74/3.81  Index Insertion      : 0.00
% 10.74/3.81  Index Deletion       : 0.00
% 10.74/3.81  Index Matching       : 0.00
% 10.74/3.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
