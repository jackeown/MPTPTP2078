%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:35 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  181 (2425 expanded)
%              Number of leaves         :   40 ( 763 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 (7528 expanded)
%              Number of equality atoms :   82 (2937 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_149,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4329,plain,(
    ! [C_479,A_480,B_481] :
      ( v1_relat_1(C_479)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4342,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_4329])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5324,plain,(
    ! [A_587,B_588,C_589] :
      ( k1_relset_1(A_587,B_588,C_589) = k1_relat_1(C_589)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5343,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_5324])).

tff(c_6321,plain,(
    ! [B_705,A_706,C_707] :
      ( k1_xboole_0 = B_705
      | k1_relset_1(A_706,B_705,C_707) = A_706
      | ~ v1_funct_2(C_707,A_706,B_705)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_706,B_705))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6334,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6321])).

tff(c_6348,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5343,c_6334])).

tff(c_6349,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6348])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6358,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6349,c_34])).

tff(c_6384,plain,(
    ! [A_708] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_708)) = A_708
      | ~ r1_tarski(A_708,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4342,c_6358])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6005,plain,(
    ! [A_672,B_673,C_674,D_675] :
      ( k2_partfun1(A_672,B_673,C_674,D_675) = k7_relat_1(C_674,D_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_672,B_673)))
      | ~ v1_funct_1(C_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6012,plain,(
    ! [D_675] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_675) = k7_relat_1('#skF_4',D_675)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_6005])).

tff(c_6023,plain,(
    ! [D_675] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_675) = k7_relat_1('#skF_4',D_675) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6012])).

tff(c_1550,plain,(
    ! [C_222,A_223,B_224] :
      ( v1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1563,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1550])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_125,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_125])).

tff(c_1807,plain,(
    ! [A_271,C_272,B_273] :
      ( r1_tarski(A_271,C_272)
      | ~ r1_tarski(B_273,C_272)
      | ~ r1_tarski(A_271,B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1868,plain,(
    ! [A_280] :
      ( r1_tarski(A_280,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_280,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_129,c_1807])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2303,plain,(
    ! [A_306,A_307] :
      ( r1_tarski(A_306,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_306,A_307)
      | ~ r1_tarski(A_307,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1868,c_8])).

tff(c_3556,plain,(
    ! [B_447,A_448] :
      ( r1_tarski(k7_relat_1(B_447,A_448),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_447,'#skF_4')
      | ~ v1_relat_1(B_447) ) ),
    inference(resolution,[status(thm)],[c_32,c_2303])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1665,plain,(
    ! [C_240,B_241,A_242] :
      ( v5_relat_1(C_240,B_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1679,plain,(
    ! [A_10,B_241,A_242] :
      ( v5_relat_1(A_10,B_241)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_242,B_241)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1665])).

tff(c_3582,plain,(
    ! [B_447,A_448] :
      ( v5_relat_1(k7_relat_1(B_447,A_448),'#skF_2')
      | ~ r1_tarski(B_447,'#skF_4')
      | ~ v1_relat_1(B_447) ) ),
    inference(resolution,[status(thm)],[c_3556,c_1679])).

tff(c_1562,plain,(
    ! [A_10,A_223,B_224] :
      ( v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_223,B_224)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1550])).

tff(c_1892,plain,(
    ! [A_281] :
      ( v1_relat_1(A_281)
      | ~ r1_tarski(A_281,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1868,c_1562])).

tff(c_1896,plain,(
    ! [A_18] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_18))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_1892])).

tff(c_1907,plain,(
    ! [A_18] : v1_relat_1(k7_relat_1('#skF_4',A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_1896])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2557,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_relset_1(A_339,B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2572,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2557])).

tff(c_4055,plain,(
    ! [B_471,A_472,C_473] :
      ( k1_xboole_0 = B_471
      | k1_relset_1(A_472,B_471,C_473) = A_472
      | ~ v1_funct_2(C_473,A_472,B_471)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_472,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4065,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4055])).

tff(c_4076,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2572,c_4065])).

tff(c_4077,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4076])).

tff(c_4086,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4077,c_34])).

tff(c_4092,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_4086])).

tff(c_44,plain,(
    ! [C_33,A_31,B_32] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r1_tarski(k2_relat_1(C_33),B_32)
      | ~ r1_tarski(k1_relat_1(C_33),A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3777,plain,(
    ! [A_457,B_458,C_459,D_460] :
      ( k2_partfun1(A_457,B_458,C_459,D_460) = k7_relat_1(C_459,D_460)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_458)))
      | ~ v1_funct_1(C_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3784,plain,(
    ! [D_460] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_460) = k7_relat_1('#skF_4',D_460)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_3777])).

tff(c_3793,plain,(
    ! [D_460] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_460) = k7_relat_1('#skF_4',D_460) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3784])).

tff(c_1525,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( v1_funct_1(k2_partfun1(A_216,B_217,C_218,D_219))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1530,plain,(
    ! [D_219] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_219))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_1525])).

tff(c_1538,plain,(
    ! [D_219] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_219)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1530])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_155,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1538,c_155])).

tff(c_1542,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1549,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_3797,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3793,c_1549])).

tff(c_3811,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_3797])).

tff(c_3817,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_3811])).

tff(c_4233,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3817])).

tff(c_4236,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4092,c_4233])).

tff(c_4239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6,c_4236])).

tff(c_4240,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3817])).

tff(c_4289,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_4240])).

tff(c_4295,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_4289])).

tff(c_4316,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3582,c_4295])).

tff(c_4326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_6,c_4316])).

tff(c_4327,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_6031,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6023,c_4327])).

tff(c_4328,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4559,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4328,c_20])).

tff(c_6026,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6023,c_4559])).

tff(c_5342,plain,(
    ! [A_587,B_588,A_10] :
      ( k1_relset_1(A_587,B_588,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_587,B_588)) ) ),
    inference(resolution,[status(thm)],[c_22,c_5324])).

tff(c_6061,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6026,c_5342])).

tff(c_6030,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6023,c_4328])).

tff(c_6237,plain,(
    ! [B_689,C_690,A_691] :
      ( k1_xboole_0 = B_689
      | v1_funct_2(C_690,A_691,B_689)
      | k1_relset_1(A_691,B_689,C_690) != A_691
      | ~ m1_subset_1(C_690,k1_zfmisc_1(k2_zfmisc_1(A_691,B_689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6243,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6030,c_6237])).

tff(c_6259,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6061,c_6243])).

tff(c_6260,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6031,c_82,c_6259])).

tff(c_6393,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6384,c_6260])).

tff(c_6429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6393])).

tff(c_6430,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6444,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6430,c_16])).

tff(c_6431,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6437,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6431])).

tff(c_6474,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6444,c_6437,c_70])).

tff(c_6526,plain,(
    ! [A_722,B_723] :
      ( r1_tarski(A_722,B_723)
      | ~ m1_subset_1(A_722,k1_zfmisc_1(B_723)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6534,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6474,c_6526])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6475,plain,(
    ! [A_7] :
      ( A_7 = '#skF_1'
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6430,c_12])).

tff(c_6538,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6534,c_6475])).

tff(c_6438,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6437,c_72])).

tff(c_6547,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6538,c_6438])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6432,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_10])).

tff(c_6548,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6432])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6452,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_1',B_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6430,c_18])).

tff(c_6468,plain,(
    ! [A_712,B_713] : v1_relat_1(k2_zfmisc_1(A_712,B_713)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6470,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6452,c_6468])).

tff(c_6500,plain,(
    ! [B_717,A_718] :
      ( r1_tarski(k7_relat_1(B_717,A_718),B_717)
      | ~ v1_relat_1(B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6504,plain,(
    ! [A_718] :
      ( k7_relat_1('#skF_1',A_718) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6500,c_6475])).

tff(c_6507,plain,(
    ! [A_718] : k7_relat_1('#skF_1',A_718) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6504])).

tff(c_6540,plain,(
    ! [A_718] : k7_relat_1('#skF_4',A_718) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6538,c_6507])).

tff(c_9275,plain,(
    ! [A_1060,B_1061,C_1062,D_1063] :
      ( k2_partfun1(A_1060,B_1061,C_1062,D_1063) = k7_relat_1(C_1062,D_1063)
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(k2_zfmisc_1(A_1060,B_1061)))
      | ~ v1_funct_1(C_1062) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10267,plain,(
    ! [A_1180,B_1181,A_1182,D_1183] :
      ( k2_partfun1(A_1180,B_1181,A_1182,D_1183) = k7_relat_1(A_1182,D_1183)
      | ~ v1_funct_1(A_1182)
      | ~ r1_tarski(A_1182,k2_zfmisc_1(A_1180,B_1181)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9275])).

tff(c_10283,plain,(
    ! [A_1180,B_1181,D_1183] :
      ( k2_partfun1(A_1180,B_1181,'#skF_4',D_1183) = k7_relat_1('#skF_4',D_1183)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6548,c_10267])).

tff(c_10297,plain,(
    ! [A_1180,B_1181,D_1183] : k2_partfun1(A_1180,B_1181,'#skF_4',D_1183) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6540,c_10283])).

tff(c_6545,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6538,c_6452])).

tff(c_6549,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6437])).

tff(c_6476,plain,(
    ! [A_714] :
      ( A_714 = '#skF_1'
      | ~ r1_tarski(A_714,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6430,c_6430,c_12])).

tff(c_6492,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_6476])).

tff(c_6541,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6492])).

tff(c_6543,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6474])).

tff(c_7230,plain,(
    ! [A_807,B_808,C_809,D_810] :
      ( v1_funct_1(k2_partfun1(A_807,B_808,C_809,D_810))
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(A_807,B_808)))
      | ~ v1_funct_1(C_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7997,plain,(
    ! [B_905,C_906,D_907] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_905,C_906,D_907))
      | ~ m1_subset_1(C_906,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_906) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6545,c_7230])).

tff(c_7999,plain,(
    ! [B_905,D_907] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_905,'#skF_4',D_907))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6543,c_7997])).

tff(c_8005,plain,(
    ! [B_905,D_907] : v1_funct_1(k2_partfun1('#skF_4',B_905,'#skF_4',D_907)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7999])).

tff(c_6556,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_6538,c_6538,c_64])).

tff(c_6557,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6556])).

tff(c_6651,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_6541,c_6557])).

tff(c_8009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8005,c_6651])).

tff(c_8010,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6556])).

tff(c_8205,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6545,c_6549,c_6549,c_6541,c_6541,c_6549,c_6549,c_6541,c_6541,c_8010])).

tff(c_8206,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8205])).

tff(c_8290,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_8206])).

tff(c_10304,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10297,c_8290])).

tff(c_10310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10304])).

tff(c_10312,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8205])).

tff(c_10332,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10312,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10335,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10332,c_2])).

tff(c_10344,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6548,c_10335])).

tff(c_10311,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8205])).

tff(c_10412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6547,c_10344,c_10311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.72  
% 8.23/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.23/2.72  
% 8.23/2.72  %Foreground sorts:
% 8.23/2.72  
% 8.23/2.72  
% 8.23/2.72  %Background operators:
% 8.23/2.72  
% 8.23/2.72  
% 8.23/2.72  %Foreground operators:
% 8.23/2.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.23/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/2.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.23/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.23/2.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.23/2.72  tff('#skF_2', type, '#skF_2': $i).
% 8.23/2.72  tff('#skF_3', type, '#skF_3': $i).
% 8.23/2.72  tff('#skF_1', type, '#skF_1': $i).
% 8.23/2.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.23/2.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.23/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.23/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.23/2.72  tff('#skF_4', type, '#skF_4': $i).
% 8.23/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/2.72  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.23/2.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.23/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.23/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/2.72  
% 8.23/2.75  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 8.23/2.75  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.23/2.75  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.23/2.75  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.23/2.75  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 8.23/2.75  tff(f_129, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.23/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.23/2.75  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 8.23/2.75  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.23/2.75  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.23/2.75  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.23/2.75  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.23/2.75  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.23/2.75  tff(f_123, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.23/2.75  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.23/2.75  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.23/2.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.23/2.75  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.23/2.75  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_4329, plain, (![C_479, A_480, B_481]: (v1_relat_1(C_479) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.23/2.75  tff(c_4342, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_4329])).
% 8.23/2.75  tff(c_66, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_82, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 8.23/2.75  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_5324, plain, (![A_587, B_588, C_589]: (k1_relset_1(A_587, B_588, C_589)=k1_relat_1(C_589) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.23/2.75  tff(c_5343, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_5324])).
% 8.23/2.75  tff(c_6321, plain, (![B_705, A_706, C_707]: (k1_xboole_0=B_705 | k1_relset_1(A_706, B_705, C_707)=A_706 | ~v1_funct_2(C_707, A_706, B_705) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_706, B_705))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.23/2.75  tff(c_6334, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_6321])).
% 8.23/2.75  tff(c_6348, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5343, c_6334])).
% 8.23/2.75  tff(c_6349, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_82, c_6348])).
% 8.23/2.75  tff(c_34, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.23/2.75  tff(c_6358, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6349, c_34])).
% 8.23/2.75  tff(c_6384, plain, (![A_708]: (k1_relat_1(k7_relat_1('#skF_4', A_708))=A_708 | ~r1_tarski(A_708, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4342, c_6358])).
% 8.23/2.75  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_6005, plain, (![A_672, B_673, C_674, D_675]: (k2_partfun1(A_672, B_673, C_674, D_675)=k7_relat_1(C_674, D_675) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_672, B_673))) | ~v1_funct_1(C_674))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.23/2.75  tff(c_6012, plain, (![D_675]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_675)=k7_relat_1('#skF_4', D_675) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_6005])).
% 8.23/2.75  tff(c_6023, plain, (![D_675]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_675)=k7_relat_1('#skF_4', D_675))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6012])).
% 8.23/2.75  tff(c_1550, plain, (![C_222, A_223, B_224]: (v1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.23/2.75  tff(c_1563, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1550])).
% 8.23/2.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.23/2.75  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.23/2.75  tff(c_125, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.23/2.75  tff(c_129, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_125])).
% 8.23/2.75  tff(c_1807, plain, (![A_271, C_272, B_273]: (r1_tarski(A_271, C_272) | ~r1_tarski(B_273, C_272) | ~r1_tarski(A_271, B_273))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/2.75  tff(c_1868, plain, (![A_280]: (r1_tarski(A_280, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_280, '#skF_4'))), inference(resolution, [status(thm)], [c_129, c_1807])).
% 8.23/2.75  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/2.75  tff(c_2303, plain, (![A_306, A_307]: (r1_tarski(A_306, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_306, A_307) | ~r1_tarski(A_307, '#skF_4'))), inference(resolution, [status(thm)], [c_1868, c_8])).
% 8.23/2.75  tff(c_3556, plain, (![B_447, A_448]: (r1_tarski(k7_relat_1(B_447, A_448), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(B_447, '#skF_4') | ~v1_relat_1(B_447))), inference(resolution, [status(thm)], [c_32, c_2303])).
% 8.23/2.75  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.23/2.75  tff(c_1665, plain, (![C_240, B_241, A_242]: (v5_relat_1(C_240, B_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.23/2.75  tff(c_1679, plain, (![A_10, B_241, A_242]: (v5_relat_1(A_10, B_241) | ~r1_tarski(A_10, k2_zfmisc_1(A_242, B_241)))), inference(resolution, [status(thm)], [c_22, c_1665])).
% 8.23/2.75  tff(c_3582, plain, (![B_447, A_448]: (v5_relat_1(k7_relat_1(B_447, A_448), '#skF_2') | ~r1_tarski(B_447, '#skF_4') | ~v1_relat_1(B_447))), inference(resolution, [status(thm)], [c_3556, c_1679])).
% 8.23/2.75  tff(c_1562, plain, (![A_10, A_223, B_224]: (v1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_223, B_224)))), inference(resolution, [status(thm)], [c_22, c_1550])).
% 8.23/2.75  tff(c_1892, plain, (![A_281]: (v1_relat_1(A_281) | ~r1_tarski(A_281, '#skF_4'))), inference(resolution, [status(thm)], [c_1868, c_1562])).
% 8.23/2.75  tff(c_1896, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_1892])).
% 8.23/2.75  tff(c_1907, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_1563, c_1896])).
% 8.23/2.75  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.23/2.75  tff(c_2557, plain, (![A_339, B_340, C_341]: (k1_relset_1(A_339, B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.23/2.75  tff(c_2572, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2557])).
% 8.23/2.75  tff(c_4055, plain, (![B_471, A_472, C_473]: (k1_xboole_0=B_471 | k1_relset_1(A_472, B_471, C_473)=A_472 | ~v1_funct_2(C_473, A_472, B_471) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_472, B_471))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.23/2.75  tff(c_4065, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4055])).
% 8.23/2.75  tff(c_4076, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2572, c_4065])).
% 8.23/2.75  tff(c_4077, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_82, c_4076])).
% 8.23/2.75  tff(c_4086, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4077, c_34])).
% 8.23/2.75  tff(c_4092, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1563, c_4086])).
% 8.23/2.75  tff(c_44, plain, (![C_33, A_31, B_32]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r1_tarski(k2_relat_1(C_33), B_32) | ~r1_tarski(k1_relat_1(C_33), A_31) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.23/2.75  tff(c_3777, plain, (![A_457, B_458, C_459, D_460]: (k2_partfun1(A_457, B_458, C_459, D_460)=k7_relat_1(C_459, D_460) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_458))) | ~v1_funct_1(C_459))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.23/2.75  tff(c_3784, plain, (![D_460]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_460)=k7_relat_1('#skF_4', D_460) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_3777])).
% 8.23/2.75  tff(c_3793, plain, (![D_460]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_460)=k7_relat_1('#skF_4', D_460))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3784])).
% 8.23/2.75  tff(c_1525, plain, (![A_216, B_217, C_218, D_219]: (v1_funct_1(k2_partfun1(A_216, B_217, C_218, D_219)) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.23/2.75  tff(c_1530, plain, (![D_219]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_219)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1525])).
% 8.23/2.75  tff(c_1538, plain, (![D_219]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_219)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1530])).
% 8.23/2.75  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.23/2.75  tff(c_155, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 8.23/2.75  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1538, c_155])).
% 8.23/2.75  tff(c_1542, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 8.23/2.75  tff(c_1549, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1542])).
% 8.23/2.75  tff(c_3797, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3793, c_1549])).
% 8.23/2.75  tff(c_3811, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_3797])).
% 8.23/2.75  tff(c_3817, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_3811])).
% 8.23/2.75  tff(c_4233, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_3817])).
% 8.23/2.75  tff(c_4236, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4092, c_4233])).
% 8.23/2.75  tff(c_4239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_6, c_4236])).
% 8.23/2.75  tff(c_4240, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_3817])).
% 8.23/2.75  tff(c_4289, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_4240])).
% 8.23/2.75  tff(c_4295, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_4289])).
% 8.23/2.75  tff(c_4316, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3582, c_4295])).
% 8.23/2.75  tff(c_4326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1563, c_6, c_4316])).
% 8.23/2.75  tff(c_4327, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1542])).
% 8.23/2.75  tff(c_6031, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6023, c_4327])).
% 8.23/2.75  tff(c_4328, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1542])).
% 8.23/2.75  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.23/2.75  tff(c_4559, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_4328, c_20])).
% 8.23/2.75  tff(c_6026, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6023, c_4559])).
% 8.23/2.75  tff(c_5342, plain, (![A_587, B_588, A_10]: (k1_relset_1(A_587, B_588, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_587, B_588)))), inference(resolution, [status(thm)], [c_22, c_5324])).
% 8.23/2.75  tff(c_6061, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_6026, c_5342])).
% 8.23/2.75  tff(c_6030, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6023, c_4328])).
% 8.23/2.75  tff(c_6237, plain, (![B_689, C_690, A_691]: (k1_xboole_0=B_689 | v1_funct_2(C_690, A_691, B_689) | k1_relset_1(A_691, B_689, C_690)!=A_691 | ~m1_subset_1(C_690, k1_zfmisc_1(k2_zfmisc_1(A_691, B_689))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.23/2.75  tff(c_6243, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_6030, c_6237])).
% 8.23/2.75  tff(c_6259, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6061, c_6243])).
% 8.23/2.75  tff(c_6260, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6031, c_82, c_6259])).
% 8.23/2.75  tff(c_6393, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6384, c_6260])).
% 8.23/2.75  tff(c_6429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_6393])).
% 8.23/2.75  tff(c_6430, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 8.23/2.75  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/2.75  tff(c_6444, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6430, c_16])).
% 8.23/2.75  tff(c_6431, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 8.23/2.75  tff(c_6437, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6431])).
% 8.23/2.75  tff(c_6474, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6444, c_6437, c_70])).
% 8.23/2.75  tff(c_6526, plain, (![A_722, B_723]: (r1_tarski(A_722, B_723) | ~m1_subset_1(A_722, k1_zfmisc_1(B_723)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.23/2.75  tff(c_6534, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6474, c_6526])).
% 8.23/2.75  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.23/2.75  tff(c_6475, plain, (![A_7]: (A_7='#skF_1' | ~r1_tarski(A_7, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6430, c_12])).
% 8.23/2.75  tff(c_6538, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6534, c_6475])).
% 8.23/2.75  tff(c_6438, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6437, c_72])).
% 8.23/2.75  tff(c_6547, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6538, c_6438])).
% 8.23/2.75  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.23/2.75  tff(c_6432, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_10])).
% 8.23/2.75  tff(c_6548, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6432])).
% 8.23/2.75  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/2.75  tff(c_6452, plain, (![B_9]: (k2_zfmisc_1('#skF_1', B_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6430, c_18])).
% 8.23/2.75  tff(c_6468, plain, (![A_712, B_713]: (v1_relat_1(k2_zfmisc_1(A_712, B_713)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.23/2.75  tff(c_6470, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6452, c_6468])).
% 8.23/2.75  tff(c_6500, plain, (![B_717, A_718]: (r1_tarski(k7_relat_1(B_717, A_718), B_717) | ~v1_relat_1(B_717))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.23/2.75  tff(c_6504, plain, (![A_718]: (k7_relat_1('#skF_1', A_718)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6500, c_6475])).
% 8.23/2.75  tff(c_6507, plain, (![A_718]: (k7_relat_1('#skF_1', A_718)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6504])).
% 8.23/2.75  tff(c_6540, plain, (![A_718]: (k7_relat_1('#skF_4', A_718)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6538, c_6507])).
% 8.23/2.75  tff(c_9275, plain, (![A_1060, B_1061, C_1062, D_1063]: (k2_partfun1(A_1060, B_1061, C_1062, D_1063)=k7_relat_1(C_1062, D_1063) | ~m1_subset_1(C_1062, k1_zfmisc_1(k2_zfmisc_1(A_1060, B_1061))) | ~v1_funct_1(C_1062))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.23/2.75  tff(c_10267, plain, (![A_1180, B_1181, A_1182, D_1183]: (k2_partfun1(A_1180, B_1181, A_1182, D_1183)=k7_relat_1(A_1182, D_1183) | ~v1_funct_1(A_1182) | ~r1_tarski(A_1182, k2_zfmisc_1(A_1180, B_1181)))), inference(resolution, [status(thm)], [c_22, c_9275])).
% 8.23/2.75  tff(c_10283, plain, (![A_1180, B_1181, D_1183]: (k2_partfun1(A_1180, B_1181, '#skF_4', D_1183)=k7_relat_1('#skF_4', D_1183) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6548, c_10267])).
% 8.23/2.75  tff(c_10297, plain, (![A_1180, B_1181, D_1183]: (k2_partfun1(A_1180, B_1181, '#skF_4', D_1183)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6540, c_10283])).
% 8.23/2.75  tff(c_6545, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6538, c_6452])).
% 8.23/2.75  tff(c_6549, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6437])).
% 8.23/2.75  tff(c_6476, plain, (![A_714]: (A_714='#skF_1' | ~r1_tarski(A_714, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6430, c_6430, c_12])).
% 8.23/2.75  tff(c_6492, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_68, c_6476])).
% 8.23/2.75  tff(c_6541, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6492])).
% 8.23/2.75  tff(c_6543, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6474])).
% 8.23/2.75  tff(c_7230, plain, (![A_807, B_808, C_809, D_810]: (v1_funct_1(k2_partfun1(A_807, B_808, C_809, D_810)) | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(A_807, B_808))) | ~v1_funct_1(C_809))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.23/2.75  tff(c_7997, plain, (![B_905, C_906, D_907]: (v1_funct_1(k2_partfun1('#skF_4', B_905, C_906, D_907)) | ~m1_subset_1(C_906, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_906))), inference(superposition, [status(thm), theory('equality')], [c_6545, c_7230])).
% 8.23/2.75  tff(c_7999, plain, (![B_905, D_907]: (v1_funct_1(k2_partfun1('#skF_4', B_905, '#skF_4', D_907)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6543, c_7997])).
% 8.23/2.75  tff(c_8005, plain, (![B_905, D_907]: (v1_funct_1(k2_partfun1('#skF_4', B_905, '#skF_4', D_907)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7999])).
% 8.23/2.75  tff(c_6556, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_6538, c_6538, c_64])).
% 8.23/2.75  tff(c_6557, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6556])).
% 8.23/2.75  tff(c_6651, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_6541, c_6557])).
% 8.23/2.75  tff(c_8009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8005, c_6651])).
% 8.23/2.75  tff(c_8010, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_6556])).
% 8.23/2.75  tff(c_8205, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6545, c_6549, c_6549, c_6541, c_6541, c_6549, c_6549, c_6541, c_6541, c_8010])).
% 8.23/2.75  tff(c_8206, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8205])).
% 8.23/2.75  tff(c_8290, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_8206])).
% 8.23/2.75  tff(c_10304, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10297, c_8290])).
% 8.23/2.75  tff(c_10310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10304])).
% 8.23/2.75  tff(c_10312, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8205])).
% 8.23/2.75  tff(c_10332, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_10312, c_20])).
% 8.23/2.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.23/2.75  tff(c_10335, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_10332, c_2])).
% 8.23/2.75  tff(c_10344, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6548, c_10335])).
% 8.23/2.75  tff(c_10311, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_8205])).
% 8.23/2.75  tff(c_10412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6547, c_10344, c_10311])).
% 8.23/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.75  
% 8.23/2.75  Inference rules
% 8.23/2.75  ----------------------
% 8.23/2.75  #Ref     : 0
% 8.23/2.75  #Sup     : 2183
% 8.23/2.75  #Fact    : 0
% 8.23/2.75  #Define  : 0
% 8.23/2.75  #Split   : 24
% 8.23/2.75  #Chain   : 0
% 8.23/2.75  #Close   : 0
% 8.23/2.75  
% 8.23/2.75  Ordering : KBO
% 8.23/2.75  
% 8.23/2.75  Simplification rules
% 8.23/2.75  ----------------------
% 8.23/2.75  #Subsume      : 299
% 8.23/2.75  #Demod        : 2486
% 8.23/2.75  #Tautology    : 1023
% 8.23/2.75  #SimpNegUnit  : 6
% 8.23/2.75  #BackRed      : 44
% 8.23/2.75  
% 8.23/2.75  #Partial instantiations: 0
% 8.23/2.75  #Strategies tried      : 1
% 8.23/2.75  
% 8.23/2.75  Timing (in seconds)
% 8.23/2.75  ----------------------
% 8.39/2.75  Preprocessing        : 0.36
% 8.39/2.75  Parsing              : 0.19
% 8.39/2.75  CNF conversion       : 0.02
% 8.39/2.75  Main loop            : 1.60
% 8.39/2.75  Inferencing          : 0.56
% 8.39/2.75  Reduction            : 0.57
% 8.39/2.75  Demodulation         : 0.42
% 8.39/2.75  BG Simplification    : 0.05
% 8.39/2.75  Subsumption          : 0.30
% 8.39/2.75  Abstraction          : 0.06
% 8.39/2.75  MUC search           : 0.00
% 8.39/2.75  Cooper               : 0.00
% 8.39/2.75  Total                : 2.02
% 8.39/2.75  Index Insertion      : 0.00
% 8.39/2.75  Index Deletion       : 0.00
% 8.39/2.75  Index Matching       : 0.00
% 8.39/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
