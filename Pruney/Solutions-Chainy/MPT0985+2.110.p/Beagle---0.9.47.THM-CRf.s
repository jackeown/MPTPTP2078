%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 8.34s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :  349 (2735 expanded)
%              Number of leaves         :   49 ( 857 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (7196 expanded)
%              Number of equality atoms :  192 (2317 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_81,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_128,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9957,plain,(
    ! [C_706,A_707,B_708] :
      ( v1_relat_1(C_706)
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(A_707,B_708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9983,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_9957])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_86,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_84,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10298,plain,(
    ! [A_746,B_747,C_748] :
      ( k2_relset_1(A_746,B_747,C_748) = k2_relat_1(C_748)
      | ~ m1_subset_1(C_748,k1_zfmisc_1(k2_zfmisc_1(A_746,B_747))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10314,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_10298])).

tff(c_10326,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10314])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [A_58] :
      ( v1_funct_1(k2_funct_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_167,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_164,c_157])).

tff(c_173,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_167])).

tff(c_301,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_311,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_301])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_311])).

tff(c_322,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_331,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_381,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_331])).

tff(c_435,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_452,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_435])).

tff(c_3423,plain,(
    ! [A_305,B_306,C_307] :
      ( k2_relset_1(A_305,B_306,C_307) = k2_relat_1(C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3436,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_3423])).

tff(c_3447,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3436])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_323,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_3297,plain,(
    ! [A_289] :
      ( k1_relat_1(k2_funct_1(A_289)) = k2_relat_1(A_289)
      | ~ v2_funct_1(A_289)
      | ~ v1_funct_1(A_289)
      | ~ v1_relat_1(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_78,plain,(
    ! [A_36] :
      ( v1_funct_2(A_36,k1_relat_1(A_36),k2_relat_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4875,plain,(
    ! [A_413] :
      ( v1_funct_2(k2_funct_1(A_413),k2_relat_1(A_413),k2_relat_1(k2_funct_1(A_413)))
      | ~ v1_funct_1(k2_funct_1(A_413))
      | ~ v1_relat_1(k2_funct_1(A_413))
      | ~ v2_funct_1(A_413)
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3297,c_78])).

tff(c_4881,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3447,c_4875])).

tff(c_4903,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_323,c_4881])).

tff(c_4912,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4903])).

tff(c_4915,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4912])).

tff(c_4919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_4915])).

tff(c_4921,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4903])).

tff(c_90,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3579,plain,(
    ! [A_313,B_314,C_315] :
      ( k1_relset_1(A_313,B_314,C_315) = k1_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3614,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_3579])).

tff(c_3880,plain,(
    ! [B_341,A_342,C_343] :
      ( k1_xboole_0 = B_341
      | k1_relset_1(A_342,B_341,C_343) = A_342
      | ~ v1_funct_2(C_343,A_342,B_341)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_342,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3899,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_3880])).

tff(c_3918,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3614,c_3899])).

tff(c_3921,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3918])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3483,plain,(
    ! [A_311] :
      ( m1_subset_1(A_311,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_311),k2_relat_1(A_311))))
      | ~ v1_funct_1(A_311)
      | ~ v1_relat_1(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4094,plain,(
    ! [A_359] :
      ( r1_tarski(A_359,k2_zfmisc_1(k1_relat_1(A_359),k2_relat_1(A_359)))
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(resolution,[status(thm)],[c_3483,c_24])).

tff(c_5116,plain,(
    ! [A_422] :
      ( r1_tarski(k2_funct_1(A_422),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_422)),k1_relat_1(A_422)))
      | ~ v1_funct_1(k2_funct_1(A_422))
      | ~ v1_relat_1(k2_funct_1(A_422))
      | ~ v2_funct_1(A_422)
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4094])).

tff(c_5142,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3921,c_5116])).

tff(c_5174,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_4921,c_323,c_5142])).

tff(c_5207,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5174])).

tff(c_5220,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_3447,c_5207])).

tff(c_5222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_5220])).

tff(c_5223,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3918])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5259,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_16])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5256,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_5223,c_20])).

tff(c_3497,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3447,c_3483])).

tff(c_3512,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_3497])).

tff(c_3539,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_3512,c_24])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3555,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3539,c_10])).

tff(c_3636,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3555])).

tff(c_5438,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5256,c_3636])).

tff(c_5448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5259,c_5438])).

tff(c_5449,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3555])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_614,plain,(
    ! [C_106,B_107,A_108] :
      ( ~ v1_xboole_0(C_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(C_106))
      | ~ r2_hidden(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3344,plain,(
    ! [B_292,A_293,A_294] :
      ( ~ v1_xboole_0(B_292)
      | ~ r2_hidden(A_293,A_294)
      | ~ r1_tarski(A_294,B_292) ) ),
    inference(resolution,[status(thm)],[c_26,c_614])).

tff(c_3347,plain,(
    ! [B_292,A_1] :
      ( ~ v1_xboole_0(B_292)
      | ~ r1_tarski(A_1,B_292)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_3344])).

tff(c_3552,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3539,c_3347])).

tff(c_3556,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3552])).

tff(c_5451,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_3556])).

tff(c_5743,plain,(
    ! [B_453,A_454,C_455] :
      ( k1_xboole_0 = B_453
      | k1_relset_1(A_454,B_453,C_455) = A_454
      | ~ v1_funct_2(C_455,A_454,B_453)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_454,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5762,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_5743])).

tff(c_5778,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3614,c_5762])).

tff(c_5780,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5778])).

tff(c_5785,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5780,c_5449])).

tff(c_346,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_362,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_346])).

tff(c_382,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_394,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_362,c_382])).

tff(c_456,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_5807,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5785,c_456])).

tff(c_5812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5807])).

tff(c_5813,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5778])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5477,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5449,c_18])).

tff(c_5566,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5477])).

tff(c_5826,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5813,c_5566])).

tff(c_5848,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5813,c_5813,c_20])).

tff(c_6029,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5848,c_5449])).

tff(c_6035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5826,c_6029])).

tff(c_6037,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5477])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6068,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6037,c_6])).

tff(c_6075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5451,c_6068])).

tff(c_6076,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3552])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6081,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6076,c_8])).

tff(c_6107,plain,(
    ! [A_8] : r1_tarski('#skF_5',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_16])).

tff(c_332,plain,(
    ! [A_79] : m1_subset_1(k6_partfun1(A_79),k1_zfmisc_1(k2_zfmisc_1(A_79,A_79))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_336,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_332])).

tff(c_359,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_336,c_346])).

tff(c_388,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_359,c_382])).

tff(c_397,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_388])).

tff(c_74,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ! [A_18] : k2_funct_1(k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_93,plain,(
    ! [A_18] : k2_funct_1(k6_partfun1(A_18)) = k6_partfun1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_38])).

tff(c_415,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_93])).

tff(c_423,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_415])).

tff(c_6102,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_6081,c_423])).

tff(c_6218,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6102,c_381])).

tff(c_6223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6107,c_6218])).

tff(c_6224,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_6323,plain,(
    ! [B_478,A_479] :
      ( k1_xboole_0 = B_478
      | k1_xboole_0 = A_479
      | k2_zfmisc_1(A_479,B_478) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6326,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_6323])).

tff(c_6515,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6326])).

tff(c_6243,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6224,c_88])).

tff(c_6932,plain,(
    ! [A_534,B_535,C_536] :
      ( k1_relset_1(A_534,B_535,C_536) = k1_relat_1(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_534,B_535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6984,plain,(
    ! [C_538] :
      ( k1_relset_1('#skF_3','#skF_4',C_538) = k1_relat_1(C_538)
      | ~ m1_subset_1(C_538,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_6932])).

tff(c_6996,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6243,c_6984])).

tff(c_7229,plain,(
    ! [B_563,C_564,A_565] :
      ( k1_xboole_0 = B_563
      | v1_funct_2(C_564,A_565,B_563)
      | k1_relset_1(A_565,B_563,C_564) != A_565
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_565,B_563))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7238,plain,(
    ! [C_564] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_564,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_564) != '#skF_3'
      | ~ m1_subset_1(C_564,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_7229])).

tff(c_7325,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7238])).

tff(c_7368,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7325,c_6])).

tff(c_7364,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7325,c_7325,c_20])).

tff(c_72,plain,(
    ! [A_32,B_33] : m1_subset_1('#skF_2'(A_32,B_33),k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6248,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_72])).

tff(c_6371,plain,(
    ! [C_484,B_485,A_486] :
      ( ~ v1_xboole_0(C_484)
      | ~ m1_subset_1(B_485,k1_zfmisc_1(C_484))
      | ~ r2_hidden(A_486,B_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6384,plain,(
    ! [A_486] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_486,'#skF_2'('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6248,c_6371])).

tff(c_6578,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6384])).

tff(c_6761,plain,(
    ! [A_523,B_524,C_525] :
      ( k2_relset_1(A_523,B_524,C_525) = k2_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6865,plain,(
    ! [C_533] :
      ( k2_relset_1('#skF_3','#skF_4',C_533) = k2_relat_1(C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_6761])).

tff(c_6871,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6243,c_6865])).

tff(c_6879,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6871])).

tff(c_6707,plain,(
    ! [A_520] :
      ( m1_subset_1(A_520,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_520),k2_relat_1(A_520))))
      | ~ v1_funct_1(A_520)
      | ~ v1_relat_1(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6724,plain,(
    ! [A_520] :
      ( r1_tarski(A_520,k2_zfmisc_1(k1_relat_1(A_520),k2_relat_1(A_520)))
      | ~ v1_funct_1(A_520)
      | ~ v1_relat_1(A_520) ) ),
    inference(resolution,[status(thm)],[c_6707,c_24])).

tff(c_6884,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_6724])).

tff(c_6894,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_6884])).

tff(c_6581,plain,(
    ! [B_505,A_506,A_507] :
      ( ~ v1_xboole_0(B_505)
      | ~ r2_hidden(A_506,A_507)
      | ~ r1_tarski(A_507,B_505) ) ),
    inference(resolution,[status(thm)],[c_26,c_6371])).

tff(c_6584,plain,(
    ! [B_505,A_1] :
      ( ~ v1_xboole_0(B_505)
      | ~ r1_tarski(A_1,B_505)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_6581])).

tff(c_6902,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6894,c_6584])).

tff(c_6910,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_6578,c_6902])).

tff(c_7665,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_6910])).

tff(c_7670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7368,c_7665])).

tff(c_7672,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7238])).

tff(c_7673,plain,(
    ! [B_584,A_585,C_586] :
      ( k1_xboole_0 = B_584
      | k1_relset_1(A_585,B_584,C_586) = A_585
      | ~ v1_funct_2(C_586,A_585,B_584)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_585,B_584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7682,plain,(
    ! [C_586] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_586) = '#skF_3'
      | ~ v1_funct_2(C_586,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_586,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6224,c_7673])).

tff(c_7756,plain,(
    ! [C_591] :
      ( k1_relset_1('#skF_3','#skF_4',C_591) = '#skF_3'
      | ~ v1_funct_2(C_591,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_591,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7672,c_7682])).

tff(c_7762,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6243,c_7756])).

tff(c_7772,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6996,c_7762])).

tff(c_6684,plain,(
    ! [A_519] :
      ( k1_relat_1(k2_funct_1(A_519)) = k2_relat_1(A_519)
      | ~ v2_funct_1(A_519)
      | ~ v1_funct_1(A_519)
      | ~ v1_relat_1(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8788,plain,(
    ! [A_647] :
      ( v1_funct_2(k2_funct_1(A_647),k2_relat_1(A_647),k2_relat_1(k2_funct_1(A_647)))
      | ~ v1_funct_1(k2_funct_1(A_647))
      | ~ v1_relat_1(k2_funct_1(A_647))
      | ~ v2_funct_1(A_647)
      | ~ v1_funct_1(A_647)
      | ~ v1_relat_1(A_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6684,c_78])).

tff(c_8791,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_8788])).

tff(c_8811,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_323,c_8791])).

tff(c_8820,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8811])).

tff(c_8823,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_8820])).

tff(c_8827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_8823])).

tff(c_8829,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8811])).

tff(c_6725,plain,(
    ! [A_521] :
      ( r1_tarski(A_521,k2_zfmisc_1(k1_relat_1(A_521),k2_relat_1(A_521)))
      | ~ v1_funct_1(A_521)
      | ~ v1_relat_1(A_521) ) ),
    inference(resolution,[status(thm)],[c_6707,c_24])).

tff(c_8952,plain,(
    ! [A_652] :
      ( r1_tarski(k2_funct_1(A_652),k2_zfmisc_1(k2_relat_1(A_652),k2_relat_1(k2_funct_1(A_652))))
      | ~ v1_funct_1(k2_funct_1(A_652))
      | ~ v1_relat_1(k2_funct_1(A_652))
      | ~ v2_funct_1(A_652)
      | ~ v1_funct_1(A_652)
      | ~ v1_relat_1(A_652) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6725])).

tff(c_8975,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_8952])).

tff(c_9002,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_8829,c_323,c_8975])).

tff(c_9033,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9002])).

tff(c_9046,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_92,c_86,c_7772,c_9033])).

tff(c_9048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_9046])).

tff(c_9050,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6384])).

tff(c_9053,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9050,c_8])).

tff(c_9057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6515,c_9053])).

tff(c_9059,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6326])).

tff(c_9058,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6326])).

tff(c_9111,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9059,c_9059,c_9058])).

tff(c_9112,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9111])).

tff(c_9120,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_6243])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9080,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_5',B_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9059,c_9059,c_22])).

tff(c_9253,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_9080])).

tff(c_9078,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9059,c_9059,c_397])).

tff(c_9102,plain,(
    k6_partfun1('#skF_5') = k2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9078,c_93])).

tff(c_9109,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9078,c_9102])).

tff(c_9189,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_9109])).

tff(c_9124,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_331])).

tff(c_9368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9120,c_9253,c_9189,c_9124])).

tff(c_9369,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9111])).

tff(c_9378,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9369,c_9369,c_6243])).

tff(c_9079,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9059,c_9059,c_20])).

tff(c_9571,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9369,c_9369,c_9079])).

tff(c_9077,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9059,c_9059,c_423])).

tff(c_9449,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9369,c_9369,c_9077])).

tff(c_9382,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9369,c_331])).

tff(c_9701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9378,c_9571,c_9449,c_9382])).

tff(c_9702,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_9703,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_10237,plain,(
    ! [A_740,B_741,C_742] :
      ( k1_relset_1(A_740,B_741,C_742) = k1_relat_1(C_742)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10262,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_9703,c_10237])).

tff(c_10782,plain,(
    ! [B_787,C_788,A_789] :
      ( k1_xboole_0 = B_787
      | v1_funct_2(C_788,A_789,B_787)
      | k1_relset_1(A_789,B_787,C_788) != A_789
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_789,B_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10794,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_9703,c_10782])).

tff(c_10814,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10262,c_10794])).

tff(c_10815,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_9702,c_10814])).

tff(c_10821,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10815])).

tff(c_10824,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10821])).

tff(c_10827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9983,c_92,c_86,c_10326,c_10824])).

tff(c_10828,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10815])).

tff(c_10872,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10828,c_6])).

tff(c_10869,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10828,c_10828,c_22])).

tff(c_10015,plain,(
    ! [C_713,B_714,A_715] :
      ( ~ v1_xboole_0(C_713)
      | ~ m1_subset_1(B_714,k1_zfmisc_1(C_713))
      | ~ r2_hidden(A_715,B_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10035,plain,(
    ! [A_715] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_715,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_88,c_10015])).

tff(c_10063,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10035])).

tff(c_10972,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_10063])).

tff(c_10978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10872,c_10972])).

tff(c_10980,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10035])).

tff(c_10981,plain,(
    ! [A_792] : ~ r2_hidden(A_792,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_10035])).

tff(c_10986,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_10981])).

tff(c_10990,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10986,c_8])).

tff(c_11218,plain,(
    ! [A_802] :
      ( A_802 = '#skF_5'
      | ~ v1_xboole_0(A_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10990,c_8])).

tff(c_11225,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10980,c_11218])).

tff(c_9714,plain,(
    ! [A_685,B_686] :
      ( r1_tarski(A_685,B_686)
      | ~ m1_subset_1(A_685,k1_zfmisc_1(B_686)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9734,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_9714])).

tff(c_9771,plain,(
    ! [B_694,A_695] :
      ( B_694 = A_695
      | ~ r1_tarski(B_694,A_695)
      | ~ r1_tarski(A_695,B_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9791,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_9734,c_9771])).

tff(c_9832,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9791])).

tff(c_11230,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11225,c_9832])).

tff(c_11235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11230])).

tff(c_11236,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9791])).

tff(c_11239,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11236,c_88])).

tff(c_11286,plain,(
    ! [C_805,A_806,B_807] :
      ( v1_relat_1(C_805)
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_806,B_807))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11403,plain,(
    ! [C_818] :
      ( v1_relat_1(C_818)
      | ~ m1_subset_1(C_818,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11236,c_11286])).

tff(c_11411,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11239,c_11403])).

tff(c_11974,plain,(
    ! [A_875,B_876,C_877] :
      ( k2_relset_1(A_875,B_876,C_877) = k2_relat_1(C_877)
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(A_875,B_876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12026,plain,(
    ! [C_879] :
      ( k2_relset_1('#skF_3','#skF_4',C_879) = k2_relat_1(C_879)
      | ~ m1_subset_1(C_879,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11236,c_11974])).

tff(c_12032,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11239,c_12026])).

tff(c_12039,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_12032])).

tff(c_11739,plain,(
    ! [A_851,B_852,C_853] :
      ( k1_relset_1(A_851,B_852,C_853) = k1_relat_1(C_853)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11764,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_9703,c_11739])).

tff(c_13703,plain,(
    ! [B_959,C_960,A_961] :
      ( k1_xboole_0 = B_959
      | v1_funct_2(C_960,A_961,B_959)
      | k1_relset_1(A_961,B_959,C_960) != A_961
      | ~ m1_subset_1(C_960,k1_zfmisc_1(k2_zfmisc_1(A_961,B_959))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13721,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_9703,c_13703])).

tff(c_13740,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11764,c_13721])).

tff(c_13741,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_9702,c_13740])).

tff(c_13744,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13741])).

tff(c_13747,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_13744])).

tff(c_13750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11411,c_92,c_86,c_12039,c_13747])).

tff(c_13751,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13741])).

tff(c_11343,plain,(
    ! [B_813,A_814] :
      ( k1_xboole_0 = B_813
      | k1_xboole_0 = A_814
      | k2_zfmisc_1(A_814,B_813) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11346,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_11236,c_11343])).

tff(c_11518,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11346])).

tff(c_13772,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13751,c_11518])).

tff(c_13791,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13751,c_13751,c_22])).

tff(c_13957,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13791,c_11236])).

tff(c_13959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13772,c_13957])).

tff(c_13961,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11346])).

tff(c_13960,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11346])).

tff(c_14087,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13961,c_13961,c_13960])).

tff(c_14088,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14087])).

tff(c_13984,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13961,c_6])).

tff(c_14100,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14088,c_13984])).

tff(c_13981,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_5',B_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13961,c_13961,c_22])).

tff(c_14278,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14088,c_14088,c_13981])).

tff(c_11456,plain,(
    ! [C_822,B_823,A_824] :
      ( ~ v1_xboole_0(C_822)
      | ~ m1_subset_1(B_823,k1_zfmisc_1(C_822))
      | ~ r2_hidden(A_824,B_823) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11475,plain,(
    ! [A_824] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3'))
      | ~ r2_hidden(A_824,k2_funct_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_9703,c_11456])).

tff(c_11497,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11475])).

tff(c_14279,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14278,c_11497])).

tff(c_14282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14100,c_14279])).

tff(c_14283,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14087])).

tff(c_14296,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14283,c_13984])).

tff(c_13980,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13961,c_13961,c_20])).

tff(c_14286,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14283,c_14283,c_13980])).

tff(c_14521,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14286,c_11497])).

tff(c_14524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_14521])).

tff(c_14526,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11475])).

tff(c_14567,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14526,c_8])).

tff(c_14581,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14567,c_18])).

tff(c_14583,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14581])).

tff(c_9754,plain,(
    ! [A_690,B_691] : m1_subset_1('#skF_2'(A_690,B_691),k1_zfmisc_1(k2_zfmisc_1(A_690,B_691))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_11370,plain,(
    ! [B_816] : m1_subset_1('#skF_2'(k1_xboole_0,B_816),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_9754])).

tff(c_11384,plain,(
    ! [B_817] : r1_tarski('#skF_2'(k1_xboole_0,B_817),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11370,c_24])).

tff(c_9799,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_9771])).

tff(c_11417,plain,(
    ! [B_819] : '#skF_2'(k1_xboole_0,B_819) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11384,c_9799])).

tff(c_62,plain,(
    ! [A_32,B_33] : v1_funct_2('#skF_2'(A_32,B_33),A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_11428,plain,(
    ! [B_819] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_819) ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_62])).

tff(c_14588,plain,(
    ! [B_819] : v1_funct_2('#skF_4','#skF_4',B_819) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14583,c_14583,c_11428])).

tff(c_14529,plain,(
    ! [A_993] : ~ r2_hidden(A_993,k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11475])).

tff(c_14534,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_14529])).

tff(c_14538,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14534,c_8])).

tff(c_14544,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14538,c_9702])).

tff(c_14585,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14583,c_14544])).

tff(c_14937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14588,c_14585])).

tff(c_14938,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14581])).

tff(c_9765,plain,(
    ! [A_692] : m1_subset_1('#skF_2'(A_692,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_9754])).

tff(c_9769,plain,(
    ! [A_692] : r1_tarski('#skF_2'(A_692,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9765,c_24])).

tff(c_9773,plain,(
    ! [A_692] :
      ( '#skF_2'(A_692,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(A_692,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_9769,c_9771])).

tff(c_11262,plain,(
    ! [A_804] : '#skF_2'(A_804,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_9773])).

tff(c_11270,plain,(
    ! [A_804] : v1_funct_2(k1_xboole_0,A_804,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11262,c_62])).

tff(c_14952,plain,(
    ! [A_804] : v1_funct_2('#skF_3',A_804,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14938,c_14938,c_11270])).

tff(c_14942,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14938,c_14544])).

tff(c_15286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14952,c_14942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:49:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.34/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.50/3.14  
% 8.50/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.50/3.14  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 8.50/3.14  
% 8.50/3.14  %Foreground sorts:
% 8.50/3.14  
% 8.50/3.14  
% 8.50/3.14  %Background operators:
% 8.50/3.14  
% 8.50/3.14  
% 8.50/3.14  %Foreground operators:
% 8.50/3.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.50/3.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.50/3.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.50/3.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.50/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.50/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.50/3.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.50/3.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.50/3.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.50/3.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.50/3.14  tff('#skF_5', type, '#skF_5': $i).
% 8.50/3.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.50/3.14  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.50/3.14  tff('#skF_3', type, '#skF_3': $i).
% 8.50/3.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.50/3.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.50/3.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.50/3.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.50/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.50/3.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.50/3.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.50/3.14  tff('#skF_4', type, '#skF_4': $i).
% 8.50/3.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.50/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.50/3.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.50/3.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.50/3.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.50/3.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.50/3.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.50/3.14  
% 8.81/3.18  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.81/3.18  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.81/3.18  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.81/3.18  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.81/3.18  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.81/3.18  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.81/3.18  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.81/3.18  tff(f_140, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 8.81/3.18  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.81/3.18  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.81/3.18  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.81/3.18  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.81/3.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.81/3.18  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.81/3.18  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.81/3.18  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.81/3.18  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.81/3.18  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.81/3.18  tff(f_81, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 8.81/3.18  tff(f_128, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 8.81/3.18  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.81/3.18  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_9957, plain, (![C_706, A_707, B_708]: (v1_relat_1(C_706) | ~m1_subset_1(C_706, k1_zfmisc_1(k2_zfmisc_1(A_707, B_708))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.81/3.18  tff(c_9983, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_9957])).
% 8.81/3.18  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_86, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_84, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_10298, plain, (![A_746, B_747, C_748]: (k2_relset_1(A_746, B_747, C_748)=k2_relat_1(C_748) | ~m1_subset_1(C_748, k1_zfmisc_1(k2_zfmisc_1(A_746, B_747))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.81/3.18  tff(c_10314, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_10298])).
% 8.81/3.18  tff(c_10326, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10314])).
% 8.81/3.18  tff(c_36, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.81/3.18  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.81/3.18  tff(c_164, plain, (![A_58]: (v1_funct_1(k2_funct_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.81/3.18  tff(c_82, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_157, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_82])).
% 8.81/3.18  tff(c_167, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_164, c_157])).
% 8.81/3.18  tff(c_173, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_167])).
% 8.81/3.18  tff(c_301, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.81/3.18  tff(c_311, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_301])).
% 8.81/3.18  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_311])).
% 8.81/3.18  tff(c_322, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_82])).
% 8.81/3.18  tff(c_331, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_322])).
% 8.81/3.18  tff(c_381, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_331])).
% 8.81/3.18  tff(c_435, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.81/3.18  tff(c_452, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_435])).
% 8.81/3.18  tff(c_3423, plain, (![A_305, B_306, C_307]: (k2_relset_1(A_305, B_306, C_307)=k2_relat_1(C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.81/3.18  tff(c_3436, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_3423])).
% 8.81/3.18  tff(c_3447, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3436])).
% 8.81/3.18  tff(c_32, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.81/3.18  tff(c_323, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_82])).
% 8.81/3.18  tff(c_3297, plain, (![A_289]: (k1_relat_1(k2_funct_1(A_289))=k2_relat_1(A_289) | ~v2_funct_1(A_289) | ~v1_funct_1(A_289) | ~v1_relat_1(A_289))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.81/3.18  tff(c_78, plain, (![A_36]: (v1_funct_2(A_36, k1_relat_1(A_36), k2_relat_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.81/3.18  tff(c_4875, plain, (![A_413]: (v1_funct_2(k2_funct_1(A_413), k2_relat_1(A_413), k2_relat_1(k2_funct_1(A_413))) | ~v1_funct_1(k2_funct_1(A_413)) | ~v1_relat_1(k2_funct_1(A_413)) | ~v2_funct_1(A_413) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(superposition, [status(thm), theory('equality')], [c_3297, c_78])).
% 8.81/3.18  tff(c_4881, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3447, c_4875])).
% 8.81/3.18  tff(c_4903, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_323, c_4881])).
% 8.81/3.18  tff(c_4912, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4903])).
% 8.81/3.18  tff(c_4915, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_4912])).
% 8.81/3.18  tff(c_4919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_4915])).
% 8.81/3.18  tff(c_4921, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4903])).
% 8.81/3.18  tff(c_90, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.81/3.18  tff(c_3579, plain, (![A_313, B_314, C_315]: (k1_relset_1(A_313, B_314, C_315)=k1_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.81/3.18  tff(c_3614, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_3579])).
% 8.81/3.18  tff(c_3880, plain, (![B_341, A_342, C_343]: (k1_xboole_0=B_341 | k1_relset_1(A_342, B_341, C_343)=A_342 | ~v1_funct_2(C_343, A_342, B_341) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_342, B_341))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_3899, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_3880])).
% 8.81/3.18  tff(c_3918, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3614, c_3899])).
% 8.81/3.18  tff(c_3921, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3918])).
% 8.81/3.18  tff(c_34, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.81/3.18  tff(c_3483, plain, (![A_311]: (m1_subset_1(A_311, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_311), k2_relat_1(A_311)))) | ~v1_funct_1(A_311) | ~v1_relat_1(A_311))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.81/3.18  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.81/3.18  tff(c_4094, plain, (![A_359]: (r1_tarski(A_359, k2_zfmisc_1(k1_relat_1(A_359), k2_relat_1(A_359))) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(resolution, [status(thm)], [c_3483, c_24])).
% 8.81/3.18  tff(c_5116, plain, (![A_422]: (r1_tarski(k2_funct_1(A_422), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_422)), k1_relat_1(A_422))) | ~v1_funct_1(k2_funct_1(A_422)) | ~v1_relat_1(k2_funct_1(A_422)) | ~v2_funct_1(A_422) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4094])).
% 8.81/3.18  tff(c_5142, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3921, c_5116])).
% 8.81/3.18  tff(c_5174, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_4921, c_323, c_5142])).
% 8.81/3.18  tff(c_5207, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_5174])).
% 8.81/3.18  tff(c_5220, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_3447, c_5207])).
% 8.81/3.18  tff(c_5222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_5220])).
% 8.81/3.18  tff(c_5223, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3918])).
% 8.81/3.18  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.81/3.18  tff(c_5259, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_16])).
% 8.81/3.18  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.81/3.18  tff(c_5256, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_5223, c_20])).
% 8.81/3.18  tff(c_3497, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3447, c_3483])).
% 8.81/3.18  tff(c_3512, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_3497])).
% 8.81/3.18  tff(c_3539, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_3512, c_24])).
% 8.81/3.18  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.81/3.18  tff(c_3555, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_3539, c_10])).
% 8.81/3.18  tff(c_3636, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3555])).
% 8.81/3.18  tff(c_5438, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5256, c_3636])).
% 8.81/3.18  tff(c_5448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5259, c_5438])).
% 8.81/3.18  tff(c_5449, plain, (k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_3555])).
% 8.81/3.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/3.18  tff(c_614, plain, (![C_106, B_107, A_108]: (~v1_xboole_0(C_106) | ~m1_subset_1(B_107, k1_zfmisc_1(C_106)) | ~r2_hidden(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.81/3.18  tff(c_3344, plain, (![B_292, A_293, A_294]: (~v1_xboole_0(B_292) | ~r2_hidden(A_293, A_294) | ~r1_tarski(A_294, B_292))), inference(resolution, [status(thm)], [c_26, c_614])).
% 8.81/3.18  tff(c_3347, plain, (![B_292, A_1]: (~v1_xboole_0(B_292) | ~r1_tarski(A_1, B_292) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_3344])).
% 8.81/3.18  tff(c_3552, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3539, c_3347])).
% 8.81/3.18  tff(c_3556, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_3552])).
% 8.81/3.18  tff(c_5451, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5449, c_3556])).
% 8.81/3.18  tff(c_5743, plain, (![B_453, A_454, C_455]: (k1_xboole_0=B_453 | k1_relset_1(A_454, B_453, C_455)=A_454 | ~v1_funct_2(C_455, A_454, B_453) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_454, B_453))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_5762, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_5743])).
% 8.81/3.18  tff(c_5778, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3614, c_5762])).
% 8.81/3.18  tff(c_5780, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5778])).
% 8.81/3.18  tff(c_5785, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5780, c_5449])).
% 8.81/3.18  tff(c_346, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.81/3.18  tff(c_362, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_346])).
% 8.81/3.18  tff(c_382, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.81/3.18  tff(c_394, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_362, c_382])).
% 8.81/3.18  tff(c_456, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_394])).
% 8.81/3.18  tff(c_5807, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5785, c_456])).
% 8.81/3.18  tff(c_5812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_5807])).
% 8.81/3.18  tff(c_5813, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5778])).
% 8.81/3.18  tff(c_18, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.81/3.18  tff(c_5477, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5449, c_18])).
% 8.81/3.18  tff(c_5566, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_5477])).
% 8.81/3.18  tff(c_5826, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5813, c_5566])).
% 8.81/3.18  tff(c_5848, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5813, c_5813, c_20])).
% 8.81/3.18  tff(c_6029, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5848, c_5449])).
% 8.81/3.18  tff(c_6035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5826, c_6029])).
% 8.81/3.18  tff(c_6037, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_5477])).
% 8.81/3.18  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.81/3.18  tff(c_6068, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6037, c_6])).
% 8.81/3.18  tff(c_6075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5451, c_6068])).
% 8.81/3.18  tff(c_6076, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_3552])).
% 8.81/3.18  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.81/3.18  tff(c_6081, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_6076, c_8])).
% 8.81/3.18  tff(c_6107, plain, (![A_8]: (r1_tarski('#skF_5', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_16])).
% 8.81/3.18  tff(c_332, plain, (![A_79]: (m1_subset_1(k6_partfun1(A_79), k1_zfmisc_1(k2_zfmisc_1(A_79, A_79))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.81/3.18  tff(c_336, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_332])).
% 8.81/3.18  tff(c_359, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_336, c_346])).
% 8.81/3.18  tff(c_388, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_359, c_382])).
% 8.81/3.18  tff(c_397, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_388])).
% 8.81/3.18  tff(c_74, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.81/3.18  tff(c_38, plain, (![A_18]: (k2_funct_1(k6_relat_1(A_18))=k6_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.81/3.18  tff(c_93, plain, (![A_18]: (k2_funct_1(k6_partfun1(A_18))=k6_partfun1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_38])).
% 8.81/3.18  tff(c_415, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_93])).
% 8.81/3.18  tff(c_423, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_397, c_415])).
% 8.81/3.18  tff(c_6102, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_6081, c_423])).
% 8.81/3.18  tff(c_6218, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6102, c_381])).
% 8.81/3.18  tff(c_6223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6107, c_6218])).
% 8.81/3.18  tff(c_6224, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_394])).
% 8.81/3.18  tff(c_6323, plain, (![B_478, A_479]: (k1_xboole_0=B_478 | k1_xboole_0=A_479 | k2_zfmisc_1(A_479, B_478)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.81/3.18  tff(c_6326, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6224, c_6323])).
% 8.81/3.18  tff(c_6515, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_6326])).
% 8.81/3.18  tff(c_6243, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6224, c_88])).
% 8.81/3.18  tff(c_6932, plain, (![A_534, B_535, C_536]: (k1_relset_1(A_534, B_535, C_536)=k1_relat_1(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_534, B_535))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.81/3.18  tff(c_6984, plain, (![C_538]: (k1_relset_1('#skF_3', '#skF_4', C_538)=k1_relat_1(C_538) | ~m1_subset_1(C_538, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6224, c_6932])).
% 8.81/3.18  tff(c_6996, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6243, c_6984])).
% 8.81/3.18  tff(c_7229, plain, (![B_563, C_564, A_565]: (k1_xboole_0=B_563 | v1_funct_2(C_564, A_565, B_563) | k1_relset_1(A_565, B_563, C_564)!=A_565 | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_565, B_563))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_7238, plain, (![C_564]: (k1_xboole_0='#skF_4' | v1_funct_2(C_564, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_564)!='#skF_3' | ~m1_subset_1(C_564, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6224, c_7229])).
% 8.81/3.18  tff(c_7325, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7238])).
% 8.81/3.18  tff(c_7368, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7325, c_6])).
% 8.81/3.18  tff(c_7364, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7325, c_7325, c_20])).
% 8.81/3.18  tff(c_72, plain, (![A_32, B_33]: (m1_subset_1('#skF_2'(A_32, B_33), k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.18  tff(c_6248, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6224, c_72])).
% 8.81/3.18  tff(c_6371, plain, (![C_484, B_485, A_486]: (~v1_xboole_0(C_484) | ~m1_subset_1(B_485, k1_zfmisc_1(C_484)) | ~r2_hidden(A_486, B_485))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.81/3.18  tff(c_6384, plain, (![A_486]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_486, '#skF_2'('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_6248, c_6371])).
% 8.81/3.18  tff(c_6578, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_6384])).
% 8.81/3.18  tff(c_6761, plain, (![A_523, B_524, C_525]: (k2_relset_1(A_523, B_524, C_525)=k2_relat_1(C_525) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.81/3.18  tff(c_6865, plain, (![C_533]: (k2_relset_1('#skF_3', '#skF_4', C_533)=k2_relat_1(C_533) | ~m1_subset_1(C_533, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6224, c_6761])).
% 8.81/3.18  tff(c_6871, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6243, c_6865])).
% 8.81/3.18  tff(c_6879, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6871])).
% 8.81/3.18  tff(c_6707, plain, (![A_520]: (m1_subset_1(A_520, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_520), k2_relat_1(A_520)))) | ~v1_funct_1(A_520) | ~v1_relat_1(A_520))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.81/3.18  tff(c_6724, plain, (![A_520]: (r1_tarski(A_520, k2_zfmisc_1(k1_relat_1(A_520), k2_relat_1(A_520))) | ~v1_funct_1(A_520) | ~v1_relat_1(A_520))), inference(resolution, [status(thm)], [c_6707, c_24])).
% 8.81/3.18  tff(c_6884, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6879, c_6724])).
% 8.81/3.18  tff(c_6894, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_6884])).
% 8.81/3.18  tff(c_6581, plain, (![B_505, A_506, A_507]: (~v1_xboole_0(B_505) | ~r2_hidden(A_506, A_507) | ~r1_tarski(A_507, B_505))), inference(resolution, [status(thm)], [c_26, c_6371])).
% 8.81/3.18  tff(c_6584, plain, (![B_505, A_1]: (~v1_xboole_0(B_505) | ~r1_tarski(A_1, B_505) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_6581])).
% 8.81/3.18  tff(c_6902, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6894, c_6584])).
% 8.81/3.18  tff(c_6910, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_6578, c_6902])).
% 8.81/3.18  tff(c_7665, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_6910])).
% 8.81/3.18  tff(c_7670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7368, c_7665])).
% 8.81/3.18  tff(c_7672, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_7238])).
% 8.81/3.18  tff(c_7673, plain, (![B_584, A_585, C_586]: (k1_xboole_0=B_584 | k1_relset_1(A_585, B_584, C_586)=A_585 | ~v1_funct_2(C_586, A_585, B_584) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_585, B_584))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_7682, plain, (![C_586]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_586)='#skF_3' | ~v1_funct_2(C_586, '#skF_3', '#skF_4') | ~m1_subset_1(C_586, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6224, c_7673])).
% 8.81/3.18  tff(c_7756, plain, (![C_591]: (k1_relset_1('#skF_3', '#skF_4', C_591)='#skF_3' | ~v1_funct_2(C_591, '#skF_3', '#skF_4') | ~m1_subset_1(C_591, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_7672, c_7682])).
% 8.81/3.18  tff(c_7762, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6243, c_7756])).
% 8.81/3.18  tff(c_7772, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6996, c_7762])).
% 8.81/3.18  tff(c_6684, plain, (![A_519]: (k1_relat_1(k2_funct_1(A_519))=k2_relat_1(A_519) | ~v2_funct_1(A_519) | ~v1_funct_1(A_519) | ~v1_relat_1(A_519))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.81/3.18  tff(c_8788, plain, (![A_647]: (v1_funct_2(k2_funct_1(A_647), k2_relat_1(A_647), k2_relat_1(k2_funct_1(A_647))) | ~v1_funct_1(k2_funct_1(A_647)) | ~v1_relat_1(k2_funct_1(A_647)) | ~v2_funct_1(A_647) | ~v1_funct_1(A_647) | ~v1_relat_1(A_647))), inference(superposition, [status(thm), theory('equality')], [c_6684, c_78])).
% 8.81/3.18  tff(c_8791, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6879, c_8788])).
% 8.81/3.18  tff(c_8811, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_323, c_8791])).
% 8.81/3.18  tff(c_8820, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_8811])).
% 8.81/3.18  tff(c_8823, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_8820])).
% 8.81/3.18  tff(c_8827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_8823])).
% 8.81/3.18  tff(c_8829, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_8811])).
% 8.81/3.18  tff(c_6725, plain, (![A_521]: (r1_tarski(A_521, k2_zfmisc_1(k1_relat_1(A_521), k2_relat_1(A_521))) | ~v1_funct_1(A_521) | ~v1_relat_1(A_521))), inference(resolution, [status(thm)], [c_6707, c_24])).
% 8.81/3.18  tff(c_8952, plain, (![A_652]: (r1_tarski(k2_funct_1(A_652), k2_zfmisc_1(k2_relat_1(A_652), k2_relat_1(k2_funct_1(A_652)))) | ~v1_funct_1(k2_funct_1(A_652)) | ~v1_relat_1(k2_funct_1(A_652)) | ~v2_funct_1(A_652) | ~v1_funct_1(A_652) | ~v1_relat_1(A_652))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6725])).
% 8.81/3.18  tff(c_8975, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6879, c_8952])).
% 8.81/3.18  tff(c_9002, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_8829, c_323, c_8975])).
% 8.81/3.18  tff(c_9033, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_9002])).
% 8.81/3.18  tff(c_9046, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_92, c_86, c_7772, c_9033])).
% 8.81/3.18  tff(c_9048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_9046])).
% 8.81/3.18  tff(c_9050, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_6384])).
% 8.81/3.18  tff(c_9053, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_9050, c_8])).
% 8.81/3.18  tff(c_9057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6515, c_9053])).
% 8.81/3.18  tff(c_9059, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6326])).
% 8.81/3.18  tff(c_9058, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6326])).
% 8.81/3.18  tff(c_9111, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9059, c_9059, c_9058])).
% 8.81/3.18  tff(c_9112, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_9111])).
% 8.81/3.18  tff(c_9120, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_6243])).
% 8.81/3.18  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.81/3.18  tff(c_9080, plain, (![B_10]: (k2_zfmisc_1('#skF_5', B_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9059, c_9059, c_22])).
% 8.81/3.18  tff(c_9253, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_9080])).
% 8.81/3.18  tff(c_9078, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9059, c_9059, c_397])).
% 8.81/3.18  tff(c_9102, plain, (k6_partfun1('#skF_5')=k2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9078, c_93])).
% 8.81/3.18  tff(c_9109, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9078, c_9102])).
% 8.81/3.18  tff(c_9189, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_9109])).
% 8.81/3.18  tff(c_9124, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_331])).
% 8.81/3.18  tff(c_9368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9120, c_9253, c_9189, c_9124])).
% 8.81/3.18  tff(c_9369, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_9111])).
% 8.81/3.18  tff(c_9378, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9369, c_9369, c_6243])).
% 8.81/3.18  tff(c_9079, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9059, c_9059, c_20])).
% 8.81/3.18  tff(c_9571, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9369, c_9369, c_9079])).
% 8.81/3.18  tff(c_9077, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9059, c_9059, c_423])).
% 8.81/3.18  tff(c_9449, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9369, c_9369, c_9077])).
% 8.81/3.18  tff(c_9382, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9369, c_331])).
% 8.81/3.18  tff(c_9701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9378, c_9571, c_9449, c_9382])).
% 8.81/3.18  tff(c_9702, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_322])).
% 8.81/3.18  tff(c_9703, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_322])).
% 8.81/3.18  tff(c_10237, plain, (![A_740, B_741, C_742]: (k1_relset_1(A_740, B_741, C_742)=k1_relat_1(C_742) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.81/3.18  tff(c_10262, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_9703, c_10237])).
% 8.81/3.18  tff(c_10782, plain, (![B_787, C_788, A_789]: (k1_xboole_0=B_787 | v1_funct_2(C_788, A_789, B_787) | k1_relset_1(A_789, B_787, C_788)!=A_789 | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_789, B_787))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_10794, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_9703, c_10782])).
% 8.81/3.18  tff(c_10814, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10262, c_10794])).
% 8.81/3.18  tff(c_10815, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_9702, c_10814])).
% 8.81/3.18  tff(c_10821, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_10815])).
% 8.81/3.18  tff(c_10824, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_10821])).
% 8.81/3.18  tff(c_10827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9983, c_92, c_86, c_10326, c_10824])).
% 8.81/3.18  tff(c_10828, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10815])).
% 8.81/3.18  tff(c_10872, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10828, c_6])).
% 8.81/3.18  tff(c_10869, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10828, c_10828, c_22])).
% 8.81/3.18  tff(c_10015, plain, (![C_713, B_714, A_715]: (~v1_xboole_0(C_713) | ~m1_subset_1(B_714, k1_zfmisc_1(C_713)) | ~r2_hidden(A_715, B_714))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.81/3.18  tff(c_10035, plain, (![A_715]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_715, '#skF_5'))), inference(resolution, [status(thm)], [c_88, c_10015])).
% 8.81/3.18  tff(c_10063, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_10035])).
% 8.81/3.18  tff(c_10972, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_10063])).
% 8.81/3.18  tff(c_10978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10872, c_10972])).
% 8.81/3.18  tff(c_10980, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_10035])).
% 8.81/3.18  tff(c_10981, plain, (![A_792]: (~r2_hidden(A_792, '#skF_5'))), inference(splitRight, [status(thm)], [c_10035])).
% 8.81/3.18  tff(c_10986, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_10981])).
% 8.81/3.18  tff(c_10990, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_10986, c_8])).
% 8.81/3.18  tff(c_11218, plain, (![A_802]: (A_802='#skF_5' | ~v1_xboole_0(A_802))), inference(demodulation, [status(thm), theory('equality')], [c_10990, c_8])).
% 8.81/3.18  tff(c_11225, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_10980, c_11218])).
% 8.81/3.18  tff(c_9714, plain, (![A_685, B_686]: (r1_tarski(A_685, B_686) | ~m1_subset_1(A_685, k1_zfmisc_1(B_686)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.81/3.18  tff(c_9734, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_9714])).
% 8.81/3.18  tff(c_9771, plain, (![B_694, A_695]: (B_694=A_695 | ~r1_tarski(B_694, A_695) | ~r1_tarski(A_695, B_694))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.81/3.18  tff(c_9791, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_9734, c_9771])).
% 8.81/3.18  tff(c_9832, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_9791])).
% 8.81/3.18  tff(c_11230, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11225, c_9832])).
% 8.81/3.18  tff(c_11235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_11230])).
% 8.81/3.18  tff(c_11236, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_9791])).
% 8.81/3.18  tff(c_11239, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11236, c_88])).
% 8.81/3.18  tff(c_11286, plain, (![C_805, A_806, B_807]: (v1_relat_1(C_805) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_806, B_807))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.81/3.18  tff(c_11403, plain, (![C_818]: (v1_relat_1(C_818) | ~m1_subset_1(C_818, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11236, c_11286])).
% 8.81/3.18  tff(c_11411, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_11239, c_11403])).
% 8.81/3.18  tff(c_11974, plain, (![A_875, B_876, C_877]: (k2_relset_1(A_875, B_876, C_877)=k2_relat_1(C_877) | ~m1_subset_1(C_877, k1_zfmisc_1(k2_zfmisc_1(A_875, B_876))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.81/3.18  tff(c_12026, plain, (![C_879]: (k2_relset_1('#skF_3', '#skF_4', C_879)=k2_relat_1(C_879) | ~m1_subset_1(C_879, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11236, c_11974])).
% 8.81/3.18  tff(c_12032, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_11239, c_12026])).
% 8.81/3.18  tff(c_12039, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_12032])).
% 8.81/3.18  tff(c_11739, plain, (![A_851, B_852, C_853]: (k1_relset_1(A_851, B_852, C_853)=k1_relat_1(C_853) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.81/3.18  tff(c_11764, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_9703, c_11739])).
% 8.81/3.18  tff(c_13703, plain, (![B_959, C_960, A_961]: (k1_xboole_0=B_959 | v1_funct_2(C_960, A_961, B_959) | k1_relset_1(A_961, B_959, C_960)!=A_961 | ~m1_subset_1(C_960, k1_zfmisc_1(k2_zfmisc_1(A_961, B_959))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.81/3.18  tff(c_13721, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_9703, c_13703])).
% 8.81/3.18  tff(c_13740, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11764, c_13721])).
% 8.81/3.18  tff(c_13741, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_9702, c_13740])).
% 8.81/3.18  tff(c_13744, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_13741])).
% 8.81/3.18  tff(c_13747, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_13744])).
% 8.81/3.18  tff(c_13750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11411, c_92, c_86, c_12039, c_13747])).
% 8.81/3.18  tff(c_13751, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_13741])).
% 8.81/3.18  tff(c_11343, plain, (![B_813, A_814]: (k1_xboole_0=B_813 | k1_xboole_0=A_814 | k2_zfmisc_1(A_814, B_813)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.81/3.18  tff(c_11346, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_11236, c_11343])).
% 8.81/3.18  tff(c_11518, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_11346])).
% 8.81/3.18  tff(c_13772, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13751, c_11518])).
% 8.81/3.18  tff(c_13791, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13751, c_13751, c_22])).
% 8.81/3.18  tff(c_13957, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13791, c_11236])).
% 8.81/3.18  tff(c_13959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13772, c_13957])).
% 8.81/3.18  tff(c_13961, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_11346])).
% 8.81/3.18  tff(c_13960, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11346])).
% 8.81/3.18  tff(c_14087, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13961, c_13961, c_13960])).
% 8.81/3.18  tff(c_14088, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_14087])).
% 8.81/3.18  tff(c_13984, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13961, c_6])).
% 8.81/3.18  tff(c_14100, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14088, c_13984])).
% 8.81/3.18  tff(c_13981, plain, (![B_10]: (k2_zfmisc_1('#skF_5', B_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13961, c_13961, c_22])).
% 8.81/3.18  tff(c_14278, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14088, c_14088, c_13981])).
% 8.81/3.18  tff(c_11456, plain, (![C_822, B_823, A_824]: (~v1_xboole_0(C_822) | ~m1_subset_1(B_823, k1_zfmisc_1(C_822)) | ~r2_hidden(A_824, B_823))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.81/3.18  tff(c_11475, plain, (![A_824]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3')) | ~r2_hidden(A_824, k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_9703, c_11456])).
% 8.81/3.18  tff(c_11497, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_11475])).
% 8.81/3.18  tff(c_14279, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14278, c_11497])).
% 8.81/3.18  tff(c_14282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14100, c_14279])).
% 8.81/3.18  tff(c_14283, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_14087])).
% 8.81/3.18  tff(c_14296, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14283, c_13984])).
% 8.81/3.18  tff(c_13980, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13961, c_13961, c_20])).
% 8.81/3.18  tff(c_14286, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14283, c_14283, c_13980])).
% 8.81/3.18  tff(c_14521, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14286, c_11497])).
% 8.81/3.18  tff(c_14524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14296, c_14521])).
% 8.81/3.18  tff(c_14526, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_11475])).
% 8.81/3.18  tff(c_14567, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_14526, c_8])).
% 8.81/3.18  tff(c_14581, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14567, c_18])).
% 8.81/3.18  tff(c_14583, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_14581])).
% 8.81/3.18  tff(c_9754, plain, (![A_690, B_691]: (m1_subset_1('#skF_2'(A_690, B_691), k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.18  tff(c_11370, plain, (![B_816]: (m1_subset_1('#skF_2'(k1_xboole_0, B_816), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_9754])).
% 8.81/3.18  tff(c_11384, plain, (![B_817]: (r1_tarski('#skF_2'(k1_xboole_0, B_817), k1_xboole_0))), inference(resolution, [status(thm)], [c_11370, c_24])).
% 8.81/3.18  tff(c_9799, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_9771])).
% 8.81/3.18  tff(c_11417, plain, (![B_819]: ('#skF_2'(k1_xboole_0, B_819)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11384, c_9799])).
% 8.81/3.18  tff(c_62, plain, (![A_32, B_33]: (v1_funct_2('#skF_2'(A_32, B_33), A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.81/3.18  tff(c_11428, plain, (![B_819]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_819))), inference(superposition, [status(thm), theory('equality')], [c_11417, c_62])).
% 8.81/3.18  tff(c_14588, plain, (![B_819]: (v1_funct_2('#skF_4', '#skF_4', B_819))), inference(demodulation, [status(thm), theory('equality')], [c_14583, c_14583, c_11428])).
% 8.81/3.18  tff(c_14529, plain, (![A_993]: (~r2_hidden(A_993, k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_11475])).
% 8.81/3.18  tff(c_14534, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_14529])).
% 8.81/3.18  tff(c_14538, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_14534, c_8])).
% 8.81/3.18  tff(c_14544, plain, (~v1_funct_2(k1_xboole_0, '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14538, c_9702])).
% 8.81/3.18  tff(c_14585, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14583, c_14544])).
% 8.81/3.18  tff(c_14937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14588, c_14585])).
% 8.81/3.18  tff(c_14938, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14581])).
% 8.81/3.18  tff(c_9765, plain, (![A_692]: (m1_subset_1('#skF_2'(A_692, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_9754])).
% 8.81/3.18  tff(c_9769, plain, (![A_692]: (r1_tarski('#skF_2'(A_692, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_9765, c_24])).
% 8.81/3.18  tff(c_9773, plain, (![A_692]: ('#skF_2'(A_692, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2'(A_692, k1_xboole_0)))), inference(resolution, [status(thm)], [c_9769, c_9771])).
% 8.81/3.18  tff(c_11262, plain, (![A_804]: ('#skF_2'(A_804, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_9773])).
% 8.81/3.18  tff(c_11270, plain, (![A_804]: (v1_funct_2(k1_xboole_0, A_804, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11262, c_62])).
% 8.81/3.18  tff(c_14952, plain, (![A_804]: (v1_funct_2('#skF_3', A_804, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14938, c_14938, c_11270])).
% 8.81/3.18  tff(c_14942, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14938, c_14544])).
% 8.81/3.18  tff(c_15286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14952, c_14942])).
% 8.81/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/3.18  
% 8.81/3.18  Inference rules
% 8.81/3.18  ----------------------
% 8.81/3.18  #Ref     : 0
% 8.81/3.18  #Sup     : 3245
% 8.81/3.18  #Fact    : 0
% 8.81/3.18  #Define  : 0
% 8.81/3.18  #Split   : 52
% 8.81/3.18  #Chain   : 0
% 8.81/3.18  #Close   : 0
% 8.81/3.18  
% 8.81/3.18  Ordering : KBO
% 8.81/3.18  
% 8.81/3.18  Simplification rules
% 8.81/3.18  ----------------------
% 8.81/3.18  #Subsume      : 326
% 8.81/3.18  #Demod        : 5201
% 8.81/3.18  #Tautology    : 2086
% 8.81/3.18  #SimpNegUnit  : 35
% 8.81/3.18  #BackRed      : 920
% 8.81/3.18  
% 8.81/3.18  #Partial instantiations: 0
% 8.81/3.18  #Strategies tried      : 1
% 8.81/3.18  
% 8.81/3.18  Timing (in seconds)
% 8.81/3.18  ----------------------
% 8.81/3.18  Preprocessing        : 0.35
% 8.81/3.18  Parsing              : 0.19
% 8.81/3.18  CNF conversion       : 0.02
% 8.81/3.18  Main loop            : 1.98
% 8.81/3.18  Inferencing          : 0.63
% 8.81/3.18  Reduction            : 0.78
% 8.81/3.18  Demodulation         : 0.58
% 8.81/3.18  BG Simplification    : 0.06
% 8.81/3.18  Subsumption          : 0.34
% 8.81/3.18  Abstraction          : 0.08
% 8.81/3.18  MUC search           : 0.00
% 8.81/3.18  Cooper               : 0.00
% 8.81/3.18  Total                : 2.45
% 8.81/3.18  Index Insertion      : 0.00
% 8.81/3.18  Index Deletion       : 0.00
% 8.81/3.18  Index Matching       : 0.00
% 8.81/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
