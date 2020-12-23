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
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 7.13s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 833 expanded)
%              Number of leaves         :   43 ( 312 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 (2676 expanded)
%              Number of equality atoms :   67 ( 321 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_123,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_56,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_48,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_497,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_503,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_497])).

tff(c_514,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_503])).

tff(c_562,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_900,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_562])).

tff(c_907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_900])).

tff(c_908,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_1302,plain,(
    ! [B_222,E_221,A_220,C_223,D_224] :
      ( k1_xboole_0 = C_223
      | v2_funct_1(D_224)
      | ~ v2_funct_1(k1_partfun1(A_220,B_222,B_222,C_223,D_224,E_221))
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(B_222,C_223)))
      | ~ v1_funct_2(E_221,B_222,C_223)
      | ~ v1_funct_1(E_221)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_220,B_222)))
      | ~ v1_funct_2(D_224,A_220,B_222)
      | ~ v1_funct_1(D_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1304,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_1302])).

tff(c_1309,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_79,c_1304])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1309])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1348,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_10])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1346,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_1310,c_16])).

tff(c_125,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_125])).

tff(c_163,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_163])).

tff(c_249,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_1481,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_249])).

tff(c_1486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1481])).

tff(c_1487,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_1490,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_74])).

tff(c_1966,plain,(
    ! [D_301,C_302,A_303,B_304] :
      ( D_301 = C_302
      | ~ r2_relset_1(A_303,B_304,C_302,D_301)
      | ~ m1_subset_1(D_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304)))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1978,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_1966])).

tff(c_2000,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1978])).

tff(c_2023,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2000])).

tff(c_2281,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2023])).

tff(c_2288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1490,c_1487,c_72,c_68,c_2281])).

tff(c_2289,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2000])).

tff(c_2691,plain,(
    ! [C_413,A_410,E_411,D_414,B_412] :
      ( k1_xboole_0 = C_413
      | v2_funct_1(D_414)
      | ~ v2_funct_1(k1_partfun1(A_410,B_412,B_412,C_413,D_414,E_411))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(B_412,C_413)))
      | ~ v1_funct_2(E_411,B_412,C_413)
      | ~ v1_funct_1(E_411)
      | ~ m1_subset_1(D_414,k1_zfmisc_1(k2_zfmisc_1(A_410,B_412)))
      | ~ v1_funct_2(D_414,A_410,B_412)
      | ~ v1_funct_1(D_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2693,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_2691])).

tff(c_2698,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1490,c_1487,c_72,c_70,c_68,c_79,c_2693])).

tff(c_2699,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_2698])).

tff(c_2739,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2738,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_2699,c_14])).

tff(c_137,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_177,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_163])).

tff(c_1504,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_2902,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2738,c_1504])).

tff(c_2907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_2902])).

tff(c_2908,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2911,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2908,c_68])).

tff(c_4817,plain,(
    ! [B_681,F_683,D_680,C_684,A_682,E_685] :
      ( m1_subset_1(k1_partfun1(A_682,B_681,C_684,D_680,E_685,F_683),k1_zfmisc_1(k2_zfmisc_1(A_682,D_680)))
      | ~ m1_subset_1(F_683,k1_zfmisc_1(k2_zfmisc_1(C_684,D_680)))
      | ~ v1_funct_1(F_683)
      | ~ m1_subset_1(E_685,k1_zfmisc_1(k2_zfmisc_1(A_682,B_681)))
      | ~ v1_funct_1(E_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4615,plain,(
    ! [D_644,C_645,A_646,B_647] :
      ( D_644 = C_645
      | ~ r2_relset_1(A_646,B_647,C_645,D_644)
      | ~ m1_subset_1(D_644,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647)))
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4625,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_4615])).

tff(c_4644,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4625])).

tff(c_4665,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4644])).

tff(c_4820,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4817,c_4665])).

tff(c_4855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1490,c_1487,c_72,c_2911,c_2908,c_4820])).

tff(c_4856,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4644])).

tff(c_5337,plain,(
    ! [E_755,C_757,B_756,A_754,D_758] :
      ( k1_xboole_0 = C_757
      | v2_funct_1(D_758)
      | ~ v2_funct_1(k1_partfun1(A_754,B_756,B_756,C_757,D_758,E_755))
      | ~ m1_subset_1(E_755,k1_zfmisc_1(k2_zfmisc_1(B_756,C_757)))
      | ~ v1_funct_2(E_755,B_756,C_757)
      | ~ v1_funct_1(E_755)
      | ~ m1_subset_1(D_758,k1_zfmisc_1(k2_zfmisc_1(A_754,B_756)))
      | ~ v1_funct_2(D_758,A_754,B_756)
      | ~ v1_funct_1(D_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5339,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4856,c_5337])).

tff(c_5344,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1490,c_1487,c_72,c_70,c_2911,c_2908,c_79,c_5339])).

tff(c_5345,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_5344])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1495,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_12])).

tff(c_2927,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1495])).

tff(c_5373,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_2927])).

tff(c_5381,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5345,c_16])).

tff(c_5561,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5381,c_1487])).

tff(c_5563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5373,c_5561])).

tff(c_5565,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1495])).

tff(c_138,plain,(
    ! [A_58] : m1_subset_1(k6_partfun1(A_58),k1_zfmisc_1(k2_zfmisc_1(A_58,A_58))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_145,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_145,c_18])).

tff(c_165,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_154,c_163])).

tff(c_176,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_165])).

tff(c_195,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_79])).

tff(c_5570,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5565,c_195])).

tff(c_5579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_5570])).

tff(c_5580,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5626,plain,(
    ! [C_779,A_780,B_781] :
      ( v1_relat_1(C_779)
      | ~ m1_subset_1(C_779,k1_zfmisc_1(k2_zfmisc_1(A_780,B_781))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5646,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5626])).

tff(c_5782,plain,(
    ! [C_793,B_794,A_795] :
      ( v5_relat_1(C_793,B_794)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_795,B_794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5804,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_5782])).

tff(c_5893,plain,(
    ! [A_810,B_811,D_812] :
      ( r2_relset_1(A_810,B_811,D_812,D_812)
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5908,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_54,c_5893])).

tff(c_5913,plain,(
    ! [A_814,B_815,C_816] :
      ( k2_relset_1(A_814,B_815,C_816) = k2_relat_1(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5935,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5913])).

tff(c_5955,plain,(
    ! [D_820,C_821,A_822,B_823] :
      ( D_820 = C_821
      | ~ r2_relset_1(A_822,B_823,C_821,D_820)
      | ~ m1_subset_1(D_820,k1_zfmisc_1(k2_zfmisc_1(A_822,B_823)))
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(A_822,B_823))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5965,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_5955])).

tff(c_5984,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5965])).

tff(c_6009,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5984])).

tff(c_6334,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_6009])).

tff(c_6341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_6334])).

tff(c_6342,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5984])).

tff(c_6842,plain,(
    ! [A_956,B_957,C_958,D_959] :
      ( k2_relset_1(A_956,B_957,C_958) = B_957
      | ~ r2_relset_1(B_957,B_957,k1_partfun1(B_957,A_956,A_956,B_957,D_959,C_958),k6_partfun1(B_957))
      | ~ m1_subset_1(D_959,k1_zfmisc_1(k2_zfmisc_1(B_957,A_956)))
      | ~ v1_funct_2(D_959,B_957,A_956)
      | ~ v1_funct_1(D_959)
      | ~ m1_subset_1(C_958,k1_zfmisc_1(k2_zfmisc_1(A_956,B_957)))
      | ~ v1_funct_2(C_958,A_956,B_957)
      | ~ v1_funct_1(C_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6845,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6342,c_6842])).

tff(c_6850,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_5908,c_5935,c_6845])).

tff(c_44,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6859,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6850,c_44])).

tff(c_6866,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5646,c_5804,c_6850,c_6859])).

tff(c_6868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5580,c_6866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:14:34 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.13/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.53  
% 7.44/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.53  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.44/2.53  
% 7.44/2.53  %Foreground sorts:
% 7.44/2.53  
% 7.44/2.53  
% 7.44/2.53  %Background operators:
% 7.44/2.53  
% 7.44/2.53  
% 7.44/2.53  %Foreground operators:
% 7.44/2.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.44/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.44/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.44/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.44/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.44/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.44/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.44/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.44/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.44/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.44/2.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.44/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.44/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.44/2.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.44/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.44/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/2.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.44/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.44/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.44/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.44/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.44/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.44/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.44/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/2.53  
% 7.44/2.56  tff(f_169, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.44/2.56  tff(f_110, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.44/2.56  tff(f_62, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.44/2.56  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.44/2.56  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.44/2.56  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.44/2.56  tff(f_149, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.44/2.56  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.44/2.56  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.44/2.56  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.44/2.56  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.44/2.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.44/2.56  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.44/2.56  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.44/2.56  tff(f_127, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.44/2.56  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.44/2.56  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_123, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 7.44/2.56  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_56, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.44/2.56  tff(c_30, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.44/2.56  tff(c_79, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 7.44/2.56  tff(c_48, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.44/2.56  tff(c_54, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.44/2.56  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.44/2.56  tff(c_497, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.56  tff(c_503, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_497])).
% 7.44/2.56  tff(c_514, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_503])).
% 7.44/2.56  tff(c_562, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_514])).
% 7.44/2.56  tff(c_900, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_562])).
% 7.44/2.56  tff(c_907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_900])).
% 7.44/2.56  tff(c_908, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_514])).
% 7.44/2.56  tff(c_1302, plain, (![B_222, E_221, A_220, C_223, D_224]: (k1_xboole_0=C_223 | v2_funct_1(D_224) | ~v2_funct_1(k1_partfun1(A_220, B_222, B_222, C_223, D_224, E_221)) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(B_222, C_223))) | ~v1_funct_2(E_221, B_222, C_223) | ~v1_funct_1(E_221) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_220, B_222))) | ~v1_funct_2(D_224, A_220, B_222) | ~v1_funct_1(D_224))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.44/2.56  tff(c_1304, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_908, c_1302])).
% 7.44/2.56  tff(c_1309, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_79, c_1304])).
% 7.44/2.56  tff(c_1310, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_123, c_1309])).
% 7.44/2.56  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.44/2.56  tff(c_1348, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_10])).
% 7.44/2.56  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.44/2.56  tff(c_1346, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_1310, c_16])).
% 7.44/2.56  tff(c_125, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.44/2.56  tff(c_136, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_125])).
% 7.44/2.56  tff(c_163, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.56  tff(c_178, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_136, c_163])).
% 7.44/2.56  tff(c_249, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_178])).
% 7.44/2.56  tff(c_1481, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1346, c_249])).
% 7.44/2.56  tff(c_1486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1481])).
% 7.44/2.56  tff(c_1487, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_178])).
% 7.44/2.56  tff(c_1490, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_74])).
% 7.44/2.56  tff(c_1966, plain, (![D_301, C_302, A_303, B_304]: (D_301=C_302 | ~r2_relset_1(A_303, B_304, C_302, D_301) | ~m1_subset_1(D_301, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.56  tff(c_1978, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_1966])).
% 7.44/2.56  tff(c_2000, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1978])).
% 7.44/2.56  tff(c_2023, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2000])).
% 7.44/2.56  tff(c_2281, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2023])).
% 7.44/2.56  tff(c_2288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1490, c_1487, c_72, c_68, c_2281])).
% 7.44/2.56  tff(c_2289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2000])).
% 7.44/2.56  tff(c_2691, plain, (![C_413, A_410, E_411, D_414, B_412]: (k1_xboole_0=C_413 | v2_funct_1(D_414) | ~v2_funct_1(k1_partfun1(A_410, B_412, B_412, C_413, D_414, E_411)) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(B_412, C_413))) | ~v1_funct_2(E_411, B_412, C_413) | ~v1_funct_1(E_411) | ~m1_subset_1(D_414, k1_zfmisc_1(k2_zfmisc_1(A_410, B_412))) | ~v1_funct_2(D_414, A_410, B_412) | ~v1_funct_1(D_414))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.44/2.56  tff(c_2693, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2289, c_2691])).
% 7.44/2.56  tff(c_2698, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1490, c_1487, c_72, c_70, c_68, c_79, c_2693])).
% 7.44/2.56  tff(c_2699, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_123, c_2698])).
% 7.44/2.56  tff(c_2739, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_10])).
% 7.44/2.56  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.44/2.56  tff(c_2738, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_2699, c_14])).
% 7.44/2.56  tff(c_137, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_125])).
% 7.44/2.56  tff(c_177, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_137, c_163])).
% 7.44/2.56  tff(c_1504, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_177])).
% 7.44/2.56  tff(c_2902, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2738, c_1504])).
% 7.44/2.56  tff(c_2907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2739, c_2902])).
% 7.44/2.56  tff(c_2908, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 7.44/2.56  tff(c_2911, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2908, c_68])).
% 7.44/2.56  tff(c_4817, plain, (![B_681, F_683, D_680, C_684, A_682, E_685]: (m1_subset_1(k1_partfun1(A_682, B_681, C_684, D_680, E_685, F_683), k1_zfmisc_1(k2_zfmisc_1(A_682, D_680))) | ~m1_subset_1(F_683, k1_zfmisc_1(k2_zfmisc_1(C_684, D_680))) | ~v1_funct_1(F_683) | ~m1_subset_1(E_685, k1_zfmisc_1(k2_zfmisc_1(A_682, B_681))) | ~v1_funct_1(E_685))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.44/2.56  tff(c_4615, plain, (![D_644, C_645, A_646, B_647]: (D_644=C_645 | ~r2_relset_1(A_646, B_647, C_645, D_644) | ~m1_subset_1(D_644, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.56  tff(c_4625, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_4615])).
% 7.44/2.56  tff(c_4644, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4625])).
% 7.44/2.56  tff(c_4665, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4644])).
% 7.44/2.56  tff(c_4820, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4817, c_4665])).
% 7.44/2.56  tff(c_4855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1490, c_1487, c_72, c_2911, c_2908, c_4820])).
% 7.44/2.56  tff(c_4856, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4644])).
% 7.44/2.56  tff(c_5337, plain, (![E_755, C_757, B_756, A_754, D_758]: (k1_xboole_0=C_757 | v2_funct_1(D_758) | ~v2_funct_1(k1_partfun1(A_754, B_756, B_756, C_757, D_758, E_755)) | ~m1_subset_1(E_755, k1_zfmisc_1(k2_zfmisc_1(B_756, C_757))) | ~v1_funct_2(E_755, B_756, C_757) | ~v1_funct_1(E_755) | ~m1_subset_1(D_758, k1_zfmisc_1(k2_zfmisc_1(A_754, B_756))) | ~v1_funct_2(D_758, A_754, B_756) | ~v1_funct_1(D_758))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.44/2.56  tff(c_5339, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4856, c_5337])).
% 7.44/2.56  tff(c_5344, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1490, c_1487, c_72, c_70, c_2911, c_2908, c_79, c_5339])).
% 7.44/2.56  tff(c_5345, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_123, c_5344])).
% 7.44/2.56  tff(c_12, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.44/2.56  tff(c_1495, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1487, c_12])).
% 7.44/2.56  tff(c_2927, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_1495])).
% 7.44/2.56  tff(c_5373, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_2927])).
% 7.44/2.56  tff(c_5381, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5345, c_16])).
% 7.44/2.56  tff(c_5561, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5381, c_1487])).
% 7.44/2.56  tff(c_5563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5373, c_5561])).
% 7.44/2.56  tff(c_5565, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1495])).
% 7.44/2.56  tff(c_138, plain, (![A_58]: (m1_subset_1(k6_partfun1(A_58), k1_zfmisc_1(k2_zfmisc_1(A_58, A_58))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.44/2.56  tff(c_145, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 7.44/2.56  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.44/2.56  tff(c_154, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_18])).
% 7.44/2.56  tff(c_165, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_154, c_163])).
% 7.44/2.56  tff(c_176, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_165])).
% 7.44/2.56  tff(c_195, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_176, c_79])).
% 7.44/2.56  tff(c_5570, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5565, c_195])).
% 7.44/2.56  tff(c_5579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_5570])).
% 7.44/2.56  tff(c_5580, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 7.44/2.56  tff(c_5626, plain, (![C_779, A_780, B_781]: (v1_relat_1(C_779) | ~m1_subset_1(C_779, k1_zfmisc_1(k2_zfmisc_1(A_780, B_781))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.44/2.56  tff(c_5646, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_5626])).
% 7.44/2.56  tff(c_5782, plain, (![C_793, B_794, A_795]: (v5_relat_1(C_793, B_794) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_795, B_794))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.44/2.56  tff(c_5804, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_5782])).
% 7.44/2.56  tff(c_5893, plain, (![A_810, B_811, D_812]: (r2_relset_1(A_810, B_811, D_812, D_812) | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.56  tff(c_5908, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_54, c_5893])).
% 7.44/2.56  tff(c_5913, plain, (![A_814, B_815, C_816]: (k2_relset_1(A_814, B_815, C_816)=k2_relat_1(C_816) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(A_814, B_815))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.44/2.56  tff(c_5935, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_5913])).
% 7.44/2.56  tff(c_5955, plain, (![D_820, C_821, A_822, B_823]: (D_820=C_821 | ~r2_relset_1(A_822, B_823, C_821, D_820) | ~m1_subset_1(D_820, k1_zfmisc_1(k2_zfmisc_1(A_822, B_823))) | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(A_822, B_823))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.44/2.56  tff(c_5965, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_5955])).
% 7.44/2.56  tff(c_5984, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5965])).
% 7.44/2.56  tff(c_6009, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5984])).
% 7.44/2.56  tff(c_6334, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_6009])).
% 7.44/2.56  tff(c_6341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_6334])).
% 7.44/2.56  tff(c_6342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5984])).
% 7.44/2.56  tff(c_6842, plain, (![A_956, B_957, C_958, D_959]: (k2_relset_1(A_956, B_957, C_958)=B_957 | ~r2_relset_1(B_957, B_957, k1_partfun1(B_957, A_956, A_956, B_957, D_959, C_958), k6_partfun1(B_957)) | ~m1_subset_1(D_959, k1_zfmisc_1(k2_zfmisc_1(B_957, A_956))) | ~v1_funct_2(D_959, B_957, A_956) | ~v1_funct_1(D_959) | ~m1_subset_1(C_958, k1_zfmisc_1(k2_zfmisc_1(A_956, B_957))) | ~v1_funct_2(C_958, A_956, B_957) | ~v1_funct_1(C_958))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.44/2.56  tff(c_6845, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6342, c_6842])).
% 7.44/2.56  tff(c_6850, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_5908, c_5935, c_6845])).
% 7.44/2.56  tff(c_44, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.44/2.56  tff(c_6859, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6850, c_44])).
% 7.44/2.56  tff(c_6866, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5646, c_5804, c_6850, c_6859])).
% 7.44/2.56  tff(c_6868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5580, c_6866])).
% 7.44/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.56  
% 7.44/2.56  Inference rules
% 7.44/2.56  ----------------------
% 7.44/2.56  #Ref     : 0
% 7.44/2.56  #Sup     : 1506
% 7.44/2.56  #Fact    : 0
% 7.44/2.56  #Define  : 0
% 7.44/2.56  #Split   : 25
% 7.44/2.56  #Chain   : 0
% 7.44/2.56  #Close   : 0
% 7.44/2.56  
% 7.44/2.56  Ordering : KBO
% 7.44/2.56  
% 7.44/2.56  Simplification rules
% 7.44/2.56  ----------------------
% 7.44/2.56  #Subsume      : 131
% 7.44/2.56  #Demod        : 1277
% 7.44/2.56  #Tautology    : 682
% 7.44/2.56  #SimpNegUnit  : 9
% 7.44/2.56  #BackRed      : 194
% 7.44/2.56  
% 7.44/2.56  #Partial instantiations: 0
% 7.44/2.56  #Strategies tried      : 1
% 7.44/2.56  
% 7.44/2.56  Timing (in seconds)
% 7.44/2.56  ----------------------
% 7.44/2.57  Preprocessing        : 0.37
% 7.44/2.57  Parsing              : 0.20
% 7.44/2.57  CNF conversion       : 0.02
% 7.44/2.57  Main loop            : 1.42
% 7.44/2.57  Inferencing          : 0.48
% 7.44/2.57  Reduction            : 0.52
% 7.44/2.57  Demodulation         : 0.37
% 7.44/2.57  BG Simplification    : 0.05
% 7.44/2.57  Subsumption          : 0.25
% 7.44/2.57  Abstraction          : 0.05
% 7.44/2.57  MUC search           : 0.00
% 7.44/2.57  Cooper               : 0.00
% 7.44/2.57  Total                : 1.85
% 7.44/2.57  Index Insertion      : 0.00
% 7.44/2.57  Index Deletion       : 0.00
% 7.44/2.57  Index Matching       : 0.00
% 7.44/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
