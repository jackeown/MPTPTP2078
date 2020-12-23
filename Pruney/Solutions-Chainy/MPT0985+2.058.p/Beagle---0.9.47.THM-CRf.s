%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:35 EST 2020

% Result     : Theorem 13.65s
% Output     : CNFRefutation 14.28s
% Verified   : 
% Statistics : Number of formulae       :  441 (7397 expanded)
%              Number of leaves         :   39 (2222 expanded)
%              Depth                    :   19
%              Number of atoms          :  806 (19065 expanded)
%              Number of equality atoms :  286 (7706 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_10067,plain,(
    ! [C_1591,A_1592,B_1593] :
      ( v1_relat_1(C_1591)
      | ~ m1_subset_1(C_1591,k1_zfmisc_1(k2_zfmisc_1(A_1592,B_1593))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10092,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_10067])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_10519,plain,(
    ! [A_1648,B_1649,C_1650] :
      ( k2_relset_1(A_1648,B_1649,C_1650) = k2_relat_1(C_1650)
      | ~ m1_subset_1(C_1650,k1_zfmisc_1(k2_zfmisc_1(A_1648,B_1649))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10535,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_10519])).

tff(c_10551,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10535])).

tff(c_32,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_189,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_172,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_192,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_172])).

tff(c_195,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_192])).

tff(c_230,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_240,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_230])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_240])).

tff(c_255,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_275,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_284,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_275])).

tff(c_312,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_333,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_312])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_545,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_568,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_545])).

tff(c_2763,plain,(
    ! [B_273,A_274,C_275] :
      ( k1_xboole_0 = B_273
      | k1_relset_1(A_274,B_273,C_275) = A_274
      | ~ v1_funct_2(C_275,A_274,B_273)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2779,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_2763])).

tff(c_2796,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_568,c_2779])).

tff(c_2800,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2796])).

tff(c_1236,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1252,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1236])).

tff(c_1272,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_568,c_1252])).

tff(c_1276,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1272])).

tff(c_30,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_256,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_506,plain,(
    ! [A_96] :
      ( k2_relat_1(k2_funct_1(A_96)) = k1_relat_1(A_96)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,(
    ! [A_33] :
      ( v1_funct_2(A_33,k1_relat_1(A_33),k2_relat_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2030,plain,(
    ! [A_233] :
      ( v1_funct_2(k2_funct_1(A_233),k1_relat_1(k2_funct_1(A_233)),k1_relat_1(A_233))
      | ~ v1_funct_1(k2_funct_1(A_233))
      | ~ v1_relat_1(k2_funct_1(A_233))
      | ~ v2_funct_1(A_233)
      | ~ v1_funct_1(A_233)
      | ~ v1_relat_1(A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_62])).

tff(c_2033,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_2030])).

tff(c_2044,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_256,c_2033])).

tff(c_2047,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2044])).

tff(c_2050,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2047])).

tff(c_2054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_2050])).

tff(c_2056,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2044])).

tff(c_632,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_645,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_632])).

tff(c_660,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_645])).

tff(c_574,plain,(
    ! [A_103] :
      ( m1_subset_1(A_103,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_103),k2_relat_1(A_103))))
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1390,plain,(
    ! [A_188] :
      ( r1_tarski(A_188,k2_zfmisc_1(k1_relat_1(A_188),k2_relat_1(A_188)))
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(resolution,[status(thm)],[c_574,c_18])).

tff(c_2103,plain,(
    ! [A_239] :
      ( r1_tarski(k2_funct_1(A_239),k2_zfmisc_1(k2_relat_1(A_239),k2_relat_1(k2_funct_1(A_239))))
      | ~ v1_funct_1(k2_funct_1(A_239))
      | ~ v1_relat_1(k2_funct_1(A_239))
      | ~ v2_funct_1(A_239)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1390])).

tff(c_2129,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_2103])).

tff(c_2147,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_2056,c_256,c_2129])).

tff(c_2173,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2147])).

tff(c_2191,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_1276,c_2173])).

tff(c_2193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_2191])).

tff(c_2194,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_2221,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2194,c_128])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2225,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2194,c_2194,c_12])).

tff(c_60,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_665,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_60])).

tff(c_672,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_665])).

tff(c_709,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_672,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_737,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_709,c_2])).

tff(c_1079,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_2389,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_1079])).

tff(c_2399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_2389])).

tff(c_2400,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_2803,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2800,c_2400])).

tff(c_127,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_120])).

tff(c_296,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_296])).

tff(c_339,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_2830,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_339])).

tff(c_2835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2830])).

tff(c_2836,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2796])).

tff(c_2866,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2836,c_128])).

tff(c_2870,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2836,c_2836,c_12])).

tff(c_3042,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2870,c_339])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_3042])).

tff(c_3048,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_3051,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3048,c_72])).

tff(c_3380,plain,(
    ! [A_317,B_318,C_319] :
      ( k1_relset_1(A_317,B_318,C_319) = k1_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3555,plain,(
    ! [C_331] :
      ( k1_relset_1('#skF_1','#skF_2',C_331) = k1_relat_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_3380])).

tff(c_3567,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3051,c_3555])).

tff(c_5331,plain,(
    ! [B_456,A_457,C_458] :
      ( k1_xboole_0 = B_456
      | k1_relset_1(A_457,B_456,C_458) = A_457
      | ~ v1_funct_2(C_458,A_457,B_456)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_457,B_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5340,plain,(
    ! [C_458] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_458) = '#skF_1'
      | ~ v1_funct_2(C_458,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_458,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_5331])).

tff(c_5402,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5340])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3058,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_10])).

tff(c_3112,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3058])).

tff(c_5425,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_3112])).

tff(c_5570,plain,(
    ! [A_467] : k2_zfmisc_1(A_467,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_5402,c_12])).

tff(c_4073,plain,(
    ! [B_381,C_382,A_383] :
      ( k1_xboole_0 = B_381
      | v1_funct_2(C_382,A_383,B_381)
      | k1_relset_1(A_383,B_381,C_382) != A_383
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4082,plain,(
    ! [C_382] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_382,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_382) != '#skF_1'
      | ~ m1_subset_1(C_382,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_4073])).

tff(c_4146,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4082])).

tff(c_4176,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4146,c_128])).

tff(c_4180,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4146,c_4146,c_12])).

tff(c_3332,plain,(
    ! [A_311,B_312,C_313] :
      ( k2_relset_1(A_311,B_312,C_313) = k2_relat_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3438,plain,(
    ! [C_325] :
      ( k2_relset_1('#skF_1','#skF_2',C_325) = k2_relat_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_3332])).

tff(c_3441,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3051,c_3438])).

tff(c_3451,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3441])).

tff(c_3270,plain,(
    ! [A_308] :
      ( m1_subset_1(A_308,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_308),k2_relat_1(A_308))))
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3293,plain,(
    ! [A_308] :
      ( r1_tarski(A_308,k2_zfmisc_1(k1_relat_1(A_308),k2_relat_1(A_308)))
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(resolution,[status(thm)],[c_3270,c_18])).

tff(c_3458,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_3293])).

tff(c_3468,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_3458])).

tff(c_3487,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3468,c_2])).

tff(c_3649,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3487])).

tff(c_4386,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4180,c_3649])).

tff(c_4392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4176,c_4386])).

tff(c_4394,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4082])).

tff(c_4396,plain,(
    ! [B_394,A_395,C_396] :
      ( k1_xboole_0 = B_394
      | k1_relset_1(A_395,B_394,C_396) = A_395
      | ~ v1_funct_2(C_396,A_395,B_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4405,plain,(
    ! [C_396] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_396) = '#skF_1'
      | ~ v1_funct_2(C_396,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_396,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_4396])).

tff(c_4577,plain,(
    ! [C_408] :
      ( k1_relset_1('#skF_1','#skF_2',C_408) = '#skF_1'
      | ~ v1_funct_2(C_408,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_408,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4394,c_4405])).

tff(c_4580,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3051,c_4577])).

tff(c_4591,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3567,c_4580])).

tff(c_4596,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_3649])).

tff(c_4606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3048,c_4596])).

tff(c_4607,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3487])).

tff(c_5592,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5570,c_4607])).

tff(c_5634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5425,c_5592])).

tff(c_5893,plain,(
    ! [C_489] :
      ( k1_relset_1('#skF_1','#skF_2',C_489) = '#skF_1'
      | ~ v1_funct_2(C_489,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_489,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_5340])).

tff(c_5896,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3051,c_5893])).

tff(c_5907,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3567,c_5896])).

tff(c_3256,plain,(
    ! [A_307] :
      ( k1_relat_1(k2_funct_1(A_307)) = k2_relat_1(A_307)
      | ~ v2_funct_1(A_307)
      | ~ v1_funct_1(A_307)
      | ~ v1_relat_1(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6356,plain,(
    ! [A_512] :
      ( v1_funct_2(k2_funct_1(A_512),k2_relat_1(A_512),k2_relat_1(k2_funct_1(A_512)))
      | ~ v1_funct_1(k2_funct_1(A_512))
      | ~ v1_relat_1(k2_funct_1(A_512))
      | ~ v2_funct_1(A_512)
      | ~ v1_funct_1(A_512)
      | ~ v1_relat_1(A_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3256,c_62])).

tff(c_6359,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_6356])).

tff(c_6367,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_256,c_6359])).

tff(c_6368,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6367])).

tff(c_6371,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_6368])).

tff(c_6375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_6371])).

tff(c_6377,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6367])).

tff(c_3294,plain,(
    ! [A_309] :
      ( r1_tarski(A_309,k2_zfmisc_1(k1_relat_1(A_309),k2_relat_1(A_309)))
      | ~ v1_funct_1(A_309)
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_3270,c_18])).

tff(c_6497,plain,(
    ! [A_523] :
      ( r1_tarski(k2_funct_1(A_523),k2_zfmisc_1(k2_relat_1(A_523),k2_relat_1(k2_funct_1(A_523))))
      | ~ v1_funct_1(k2_funct_1(A_523))
      | ~ v1_relat_1(k2_funct_1(A_523))
      | ~ v2_funct_1(A_523)
      | ~ v1_funct_1(A_523)
      | ~ v1_relat_1(A_523) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3294])).

tff(c_6523,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3451,c_6497])).

tff(c_6541,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_6377,c_256,c_6523])).

tff(c_6567,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6541])).

tff(c_6585,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_5907,c_6567])).

tff(c_6587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_6585])).

tff(c_6589,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6612,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_6589,c_14])).

tff(c_6588,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_6710,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_6589,c_6588])).

tff(c_6711,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6710])).

tff(c_6713,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_284])).

tff(c_6718,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6612,c_6713])).

tff(c_6614,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_16])).

tff(c_6828,plain,(
    ! [A_546,B_547,C_548] :
      ( k2_relset_1(A_546,B_547,C_548) = k2_relat_1(C_548)
      | ~ m1_subset_1(C_548,k1_zfmisc_1(k2_zfmisc_1(A_546,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6849,plain,(
    ! [A_549,B_550] : k2_relset_1(A_549,B_550,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6614,c_6828])).

tff(c_6715,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_6711,c_68])).

tff(c_6853,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6849,c_6715])).

tff(c_6759,plain,(
    ! [A_535] :
      ( k1_relat_1(k2_funct_1(A_535)) = k2_relat_1(A_535)
      | ~ v2_funct_1(A_535)
      | ~ v1_funct_1(A_535)
      | ~ v1_relat_1(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8142,plain,(
    ! [A_1428] :
      ( v1_funct_2(k2_funct_1(A_1428),k2_relat_1(A_1428),k2_relat_1(k2_funct_1(A_1428)))
      | ~ v1_funct_1(k2_funct_1(A_1428))
      | ~ v1_relat_1(k2_funct_1(A_1428))
      | ~ v2_funct_1(A_1428)
      | ~ v1_funct_1(A_1428)
      | ~ v1_relat_1(A_1428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6759,c_62])).

tff(c_8145,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6853,c_8142])).

tff(c_8153,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_256,c_8145])).

tff(c_8154,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8153])).

tff(c_8157,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_8154])).

tff(c_8161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_8157])).

tff(c_8163,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8153])).

tff(c_6879,plain,(
    ! [A_553] :
      ( m1_subset_1(A_553,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_553),k2_relat_1(A_553))))
      | ~ v1_funct_1(A_553)
      | ~ v1_relat_1(A_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7686,plain,(
    ! [A_1391] :
      ( r1_tarski(A_1391,k2_zfmisc_1(k1_relat_1(A_1391),k2_relat_1(A_1391)))
      | ~ v1_funct_1(A_1391)
      | ~ v1_relat_1(A_1391) ) ),
    inference(resolution,[status(thm)],[c_6879,c_18])).

tff(c_8408,plain,(
    ! [A_1445] :
      ( r1_tarski(k2_funct_1(A_1445),k2_zfmisc_1(k2_relat_1(A_1445),k2_relat_1(k2_funct_1(A_1445))))
      | ~ v1_funct_1(k2_funct_1(A_1445))
      | ~ v1_relat_1(k2_funct_1(A_1445))
      | ~ v2_funct_1(A_1445)
      | ~ v1_funct_1(A_1445)
      | ~ v1_relat_1(A_1445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7686])).

tff(c_8434,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6853,c_8408])).

tff(c_8452,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_76,c_70,c_8163,c_256,c_6612,c_8434])).

tff(c_8454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6718,c_8452])).

tff(c_8455,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6710])).

tff(c_6613,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_6589,c_12])).

tff(c_8459,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_8455,c_6613])).

tff(c_8468,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_275])).

tff(c_8695,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8459,c_8468])).

tff(c_8466,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_333])).

tff(c_8473,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_76])).

tff(c_8472,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_70])).

tff(c_136,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_143,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_152,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_143,c_18])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_8])).

tff(c_6608,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_6589,c_156])).

tff(c_8463,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_8455,c_6608])).

tff(c_8458,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_6614])).

tff(c_8615,plain,(
    ! [A_1453,B_1454,C_1455] :
      ( k1_relset_1(A_1453,B_1454,C_1455) = k1_relat_1(C_1455)
      | ~ m1_subset_1(C_1455,k1_zfmisc_1(k2_zfmisc_1(A_1453,B_1454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8633,plain,(
    ! [A_1453,B_1454] : k1_relset_1(A_1453,B_1454,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8458,c_8615])).

tff(c_56,plain,(
    ! [A_32] : v1_partfun1(k6_partfun1(A_32),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8773,plain,(
    ! [C_1472,A_1473,B_1474] :
      ( v1_funct_2(C_1472,A_1473,B_1474)
      | ~ v1_partfun1(C_1472,A_1473)
      | ~ v1_funct_1(C_1472)
      | ~ m1_subset_1(C_1472,k1_zfmisc_1(k2_zfmisc_1(A_1473,B_1474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8793,plain,(
    ! [A_32] :
      ( v1_funct_2(k6_partfun1(A_32),A_32,A_32)
      | ~ v1_partfun1(k6_partfun1(A_32),A_32)
      | ~ v1_funct_1(k6_partfun1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_58,c_8773])).

tff(c_8801,plain,(
    ! [A_32] :
      ( v1_funct_2(k6_partfun1(A_32),A_32,A_32)
      | ~ v1_funct_1(k6_partfun1(A_32)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8793])).

tff(c_8464,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_6589])).

tff(c_52,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_79,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_8924,plain,(
    ! [B_1490,C_1491] :
      ( k1_relset_1('#skF_1',B_1490,C_1491) = '#skF_1'
      | ~ v1_funct_2(C_1491,'#skF_1',B_1490)
      | ~ m1_subset_1(C_1491,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8464,c_8464,c_8464,c_8464,c_79])).

tff(c_8929,plain,
    ( k1_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1')) = '#skF_1'
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8801,c_8924])).

tff(c_8943,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8473,c_8463,c_8458,c_8463,c_8633,c_8463,c_8929])).

tff(c_8469,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_256])).

tff(c_8479,plain,(
    ! [A_1446] :
      ( k2_relat_1(k2_funct_1(A_1446)) = k1_relat_1(A_1446)
      | ~ v2_funct_1(A_1446)
      | ~ v1_funct_1(A_1446)
      | ~ v1_relat_1(A_1446) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9635,plain,(
    ! [A_1565] :
      ( v1_funct_2(k2_funct_1(A_1565),k1_relat_1(k2_funct_1(A_1565)),k1_relat_1(A_1565))
      | ~ v1_funct_1(k2_funct_1(A_1565))
      | ~ v1_relat_1(k2_funct_1(A_1565))
      | ~ v2_funct_1(A_1565)
      | ~ v1_funct_1(A_1565)
      | ~ v1_relat_1(A_1565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8479,c_62])).

tff(c_9638,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8943,c_9635])).

tff(c_9646,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8466,c_8473,c_8472,c_8469,c_9638])).

tff(c_9647,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_9646])).

tff(c_9650,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_9647])).

tff(c_9654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8466,c_8473,c_9650])).

tff(c_9656,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_9646])).

tff(c_8659,plain,(
    ! [A_1461,B_1462,C_1463] :
      ( k2_relset_1(A_1461,B_1462,C_1463) = k2_relat_1(C_1463)
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(k2_zfmisc_1(A_1461,B_1462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8708,plain,(
    ! [A_1467,B_1468] : k2_relset_1(A_1467,B_1468,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8458,c_8659])).

tff(c_8470,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8455,c_68])).

tff(c_8712,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_8708,c_8470])).

tff(c_8729,plain,(
    ! [A_1469] :
      ( m1_subset_1(A_1469,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1469),k2_relat_1(A_1469))))
      | ~ v1_funct_1(A_1469)
      | ~ v1_relat_1(A_1469) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_9957,plain,(
    ! [A_1588] :
      ( m1_subset_1(k2_funct_1(A_1588),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1588),k2_relat_1(k2_funct_1(A_1588)))))
      | ~ v1_funct_1(k2_funct_1(A_1588))
      | ~ v1_relat_1(k2_funct_1(A_1588))
      | ~ v2_funct_1(A_1588)
      | ~ v1_funct_1(A_1588)
      | ~ v1_relat_1(A_1588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8729])).

tff(c_9986,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1')))))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8712,c_9957])).

tff(c_10005,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8466,c_8473,c_8472,c_9656,c_8469,c_9986])).

tff(c_10034,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_1'))))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_10005])).

tff(c_10053,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8466,c_8473,c_8472,c_8459,c_8943,c_10034])).

tff(c_10055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8695,c_10053])).

tff(c_10056,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_10057,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_10359,plain,(
    ! [A_1630,B_1631,C_1632] :
      ( k1_relset_1(A_1630,B_1631,C_1632) = k1_relat_1(C_1632)
      | ~ m1_subset_1(C_1632,k1_zfmisc_1(k2_zfmisc_1(A_1630,B_1631))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10383,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10057,c_10359])).

tff(c_11348,plain,(
    ! [B_1718,C_1719,A_1720] :
      ( k1_xboole_0 = B_1718
      | v1_funct_2(C_1719,A_1720,B_1718)
      | k1_relset_1(A_1720,B_1718,C_1719) != A_1720
      | ~ m1_subset_1(C_1719,k1_zfmisc_1(k2_zfmisc_1(A_1720,B_1718))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11354,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_10057,c_11348])).

tff(c_11377,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10383,c_11354])).

tff(c_11378,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10056,c_11377])).

tff(c_11388,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11378])).

tff(c_11391,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_11388])).

tff(c_11394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10092,c_76,c_70,c_10551,c_11391])).

tff(c_11395,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11378])).

tff(c_11424,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11395,c_128])).

tff(c_11427,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11395,c_11395,c_14])).

tff(c_10134,plain,(
    ! [B_1599,A_1600] :
      ( B_1599 = A_1600
      | ~ r1_tarski(B_1599,A_1600)
      | ~ r1_tarski(A_1600,B_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10147,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_10134])).

tff(c_10191,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10147])).

tff(c_11546,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11427,c_10191])).

tff(c_11551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11424,c_11546])).

tff(c_11552,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10147])).

tff(c_11555,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11552,c_72])).

tff(c_13553,plain,(
    ! [A_1863,B_1864,C_1865] :
      ( k2_relset_1(A_1863,B_1864,C_1865) = k2_relat_1(C_1865)
      | ~ m1_subset_1(C_1865,k1_zfmisc_1(k2_zfmisc_1(A_1863,B_1864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13665,plain,(
    ! [C_1877] :
      ( k2_relset_1('#skF_1','#skF_2',C_1877) = k2_relat_1(C_1877)
      | ~ m1_subset_1(C_1877,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_13553])).

tff(c_13668,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11555,c_13665])).

tff(c_13678,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13668])).

tff(c_15344,plain,(
    ! [B_1992,C_1993,A_1994] :
      ( k1_xboole_0 = B_1992
      | v1_funct_2(C_1993,A_1994,B_1992)
      | k1_relset_1(A_1994,B_1992,C_1993) != A_1994
      | ~ m1_subset_1(C_1993,k1_zfmisc_1(k2_zfmisc_1(A_1994,B_1992))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15356,plain,(
    ! [C_1993] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_1993,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_1993) != '#skF_1'
      | ~ m1_subset_1(C_1993,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_15344])).

tff(c_15434,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_15356])).

tff(c_11806,plain,(
    ! [A_1748,B_1749,C_1750] :
      ( k2_relset_1(A_1748,B_1749,C_1750) = k2_relat_1(C_1750)
      | ~ m1_subset_1(C_1750,k1_zfmisc_1(k2_zfmisc_1(A_1748,B_1749))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11879,plain,(
    ! [C_1758] :
      ( k2_relset_1('#skF_1','#skF_2',C_1758) = k2_relat_1(C_1758)
      | ~ m1_subset_1(C_1758,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_11806])).

tff(c_11882,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11555,c_11879])).

tff(c_11892,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11882])).

tff(c_11957,plain,(
    ! [A_1759,B_1760,C_1761] :
      ( k1_relset_1(A_1759,B_1760,C_1761) = k1_relat_1(C_1761)
      | ~ m1_subset_1(C_1761,k1_zfmisc_1(k2_zfmisc_1(A_1759,B_1760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11989,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10057,c_11957])).

tff(c_13187,plain,(
    ! [B_1854,C_1855,A_1856] :
      ( k1_xboole_0 = B_1854
      | v1_funct_2(C_1855,A_1856,B_1854)
      | k1_relset_1(A_1856,B_1854,C_1855) != A_1856
      | ~ m1_subset_1(C_1855,k1_zfmisc_1(k2_zfmisc_1(A_1856,B_1854))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13199,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_10057,c_13187])).

tff(c_13224,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11989,c_13199])).

tff(c_13225,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10056,c_13224])).

tff(c_13232,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13225])).

tff(c_13235,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_13232])).

tff(c_13238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10092,c_76,c_70,c_11892,c_13235])).

tff(c_13239,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13225])).

tff(c_13272,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13239,c_128])).

tff(c_13276,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13239,c_13239,c_12])).

tff(c_10066,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10057,c_18])).

tff(c_10145,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10066,c_10134])).

tff(c_11761,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10145])).

tff(c_13435,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13276,c_11761])).

tff(c_13441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13272,c_13435])).

tff(c_13442,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10145])).

tff(c_13455,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13442,c_10])).

tff(c_13514,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13455])).

tff(c_15454,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15434,c_13514])).

tff(c_15467,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15434,c_15434,c_14])).

tff(c_15617,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15467,c_13442])).

tff(c_15619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15454,c_15617])).

tff(c_15621,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15356])).

tff(c_13604,plain,(
    ! [A_1869,B_1870,C_1871] :
      ( k1_relset_1(A_1869,B_1870,C_1871) = k1_relat_1(C_1871)
      | ~ m1_subset_1(C_1871,k1_zfmisc_1(k2_zfmisc_1(A_1869,B_1870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13634,plain,(
    ! [A_1869,B_1870] : k1_relset_1(A_1869,B_1870,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_13604])).

tff(c_48,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13837,plain,(
    ! [C_1890,B_1891] :
      ( v1_funct_2(C_1890,k1_xboole_0,B_1891)
      | k1_relset_1(k1_xboole_0,B_1891,C_1890) != k1_xboole_0
      | ~ m1_subset_1(C_1890,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_13843,plain,(
    ! [B_1891] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1891)
      | k1_relset_1(k1_xboole_0,B_1891,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_13837])).

tff(c_13846,plain,(
    ! [B_1891] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1891)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13634,c_13843])).

tff(c_13847,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13846])).

tff(c_167,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_56])).

tff(c_10089,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10057,c_10067])).

tff(c_11625,plain,(
    ! [B_1728,A_1729] :
      ( v1_funct_1(B_1728)
      | ~ m1_subset_1(B_1728,k1_zfmisc_1(A_1729))
      | ~ v1_funct_1(A_1729)
      | ~ v1_relat_1(A_1729) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11651,plain,(
    ! [A_6] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_11625])).

tff(c_11654,plain,(
    ! [A_1732] :
      ( ~ v1_funct_1(A_1732)
      | ~ v1_relat_1(A_1732) ) ),
    inference(splitLeft,[status(thm)],[c_11651])).

tff(c_11663,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10089,c_11654])).

tff(c_11675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_11663])).

tff(c_11676,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11651])).

tff(c_14093,plain,(
    ! [C_1916,A_1917,B_1918] :
      ( v1_funct_2(C_1916,A_1917,B_1918)
      | ~ v1_partfun1(C_1916,A_1917)
      | ~ v1_funct_1(C_1916)
      | ~ m1_subset_1(C_1916,k1_zfmisc_1(k2_zfmisc_1(A_1917,B_1918))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14122,plain,(
    ! [A_1917,B_1918] :
      ( v1_funct_2(k1_xboole_0,A_1917,B_1918)
      | ~ v1_partfun1(k1_xboole_0,A_1917)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_14093])).

tff(c_14134,plain,(
    ! [A_1919,B_1920] :
      ( v1_funct_2(k1_xboole_0,A_1919,B_1920)
      | ~ v1_partfun1(k1_xboole_0,A_1919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11676,c_14122])).

tff(c_14137,plain,(
    ! [B_1920] :
      ( k1_relset_1(k1_xboole_0,B_1920,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14134,c_79])).

tff(c_14143,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_16,c_13634,c_14137])).

tff(c_14145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13847,c_14143])).

tff(c_14147,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13846])).

tff(c_14148,plain,(
    ! [A_1869,B_1870] : k1_relset_1(A_1869,B_1870,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14147,c_13634])).

tff(c_15373,plain,(
    ! [B_1992,A_1994] :
      ( k1_xboole_0 = B_1992
      | v1_funct_2(k1_xboole_0,A_1994,B_1992)
      | k1_relset_1(A_1994,B_1992,k1_xboole_0) != A_1994 ) ),
    inference(resolution,[status(thm)],[c_16,c_15344])).

tff(c_15380,plain,(
    ! [B_1992,A_1994] :
      ( k1_xboole_0 = B_1992
      | v1_funct_2(k1_xboole_0,A_1994,B_1992)
      | k1_xboole_0 != A_1994 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14148,c_15373])).

tff(c_15661,plain,(
    ! [B_2005,A_2006,C_2007] :
      ( k1_xboole_0 = B_2005
      | k1_relset_1(A_2006,B_2005,C_2007) = A_2006
      | ~ v1_funct_2(C_2007,A_2006,B_2005)
      | ~ m1_subset_1(C_2007,k1_zfmisc_1(k2_zfmisc_1(A_2006,B_2005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15673,plain,(
    ! [C_2007] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_2007) = '#skF_1'
      | ~ v1_funct_2(C_2007,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_2007,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_15661])).

tff(c_15870,plain,(
    ! [C_2023] :
      ( k1_relset_1('#skF_1','#skF_2',C_2023) = '#skF_1'
      | ~ v1_funct_2(C_2023,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_2023,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15621,c_15673])).

tff(c_15881,plain,
    ( k1_relset_1('#skF_1','#skF_2',k1_xboole_0) = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_15870])).

tff(c_15887,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14148,c_15881])).

tff(c_15935,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15887])).

tff(c_15976,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_1' ),
    inference(resolution,[status(thm)],[c_15380,c_15935])).

tff(c_15985,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_15621,c_15976])).

tff(c_14306,plain,(
    ! [A_1938,B_1939,A_1940] :
      ( k1_relset_1(A_1938,B_1939,A_1940) = k1_relat_1(A_1940)
      | ~ r1_tarski(A_1940,k2_zfmisc_1(A_1938,B_1939)) ) ),
    inference(resolution,[status(thm)],[c_20,c_13604])).

tff(c_14343,plain,(
    ! [A_1938,B_1939] : k1_relset_1(A_1938,B_1939,k2_zfmisc_1(A_1938,B_1939)) = k1_relat_1(k2_zfmisc_1(A_1938,B_1939)) ),
    inference(resolution,[status(thm)],[c_6,c_14306])).

tff(c_16183,plain,(
    ! [B_2039,A_2040,A_2041] :
      ( k1_xboole_0 = B_2039
      | v1_funct_2(A_2040,A_2041,B_2039)
      | k1_relset_1(A_2041,B_2039,A_2040) != A_2041
      | ~ r1_tarski(A_2040,k2_zfmisc_1(A_2041,B_2039)) ) ),
    inference(resolution,[status(thm)],[c_20,c_15344])).

tff(c_16209,plain,(
    ! [B_2039,A_2041] :
      ( k1_xboole_0 = B_2039
      | v1_funct_2(k2_zfmisc_1(A_2041,B_2039),A_2041,B_2039)
      | k1_relset_1(A_2041,B_2039,k2_zfmisc_1(A_2041,B_2039)) != A_2041 ) ),
    inference(resolution,[status(thm)],[c_6,c_16183])).

tff(c_16257,plain,(
    ! [B_2045,A_2046] :
      ( k1_xboole_0 = B_2045
      | v1_funct_2(k2_zfmisc_1(A_2046,B_2045),A_2046,B_2045)
      | k1_relat_1(k2_zfmisc_1(A_2046,B_2045)) != A_2046 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14343,c_16209])).

tff(c_16270,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13442,c_16257])).

tff(c_16291,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13442,c_16270])).

tff(c_16292,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10056,c_15985,c_16291])).

tff(c_16301,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16292])).

tff(c_16304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10092,c_76,c_70,c_13678,c_16301])).

tff(c_16305,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15887])).

tff(c_11564,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11552,c_10])).

tff(c_11607,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11564])).

tff(c_16339,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16305,c_11607])).

tff(c_16349,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16305,c_16305,c_14])).

tff(c_16642,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16349,c_11552])).

tff(c_16644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16339,c_16642])).

tff(c_16645,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13455])).

tff(c_16680,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16645])).

tff(c_16685,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16680,c_11607])).

tff(c_16695,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16680,c_16680,c_14])).

tff(c_16803,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16695,c_11552])).

tff(c_16805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16685,c_16803])).

tff(c_16806,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16645])).

tff(c_16811,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16806,c_11607])).

tff(c_16927,plain,(
    ! [A_2066] : k2_zfmisc_1(A_2066,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16806,c_16806,c_12])).

tff(c_16942,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16927,c_11552])).

tff(c_16967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16811,c_16942])).

tff(c_16969,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11564])).

tff(c_16979,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_14])).

tff(c_16968,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_11564])).

tff(c_17474,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_16968])).

tff(c_17475,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17474])).

tff(c_16976,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_128])).

tff(c_17021,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_16968])).

tff(c_17022,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17021])).

tff(c_16987,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10145])).

tff(c_17145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16976,c_16979,c_17022,c_16987])).

tff(c_17146,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17021])).

tff(c_17147,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17021])).

tff(c_17171,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_17147])).

tff(c_44,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_78,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_16977,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_3',A_29,'#skF_3')
      | A_29 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_16969,c_78])).

tff(c_17418,plain,(
    ! [A_2089] :
      ( v1_funct_2('#skF_1',A_2089,'#skF_1')
      | A_2089 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_17146,c_17146,c_16977])).

tff(c_16980,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_12])).

tff(c_17210,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_17146,c_16980])).

tff(c_17160,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_10057])).

tff(c_17337,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17210,c_17160])).

tff(c_17350,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17337,c_18])).

tff(c_16978,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_8])).

tff(c_17307,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_17146,c_16978])).

tff(c_17361,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17350,c_17307])).

tff(c_17161,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17146,c_10056])).

tff(c_17367,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17361,c_17161])).

tff(c_17421,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_17418,c_17367])).

tff(c_17425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17171,c_17421])).

tff(c_17426,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10145])).

tff(c_17565,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16979,c_17475,c_17426])).

tff(c_17673,plain,(
    ! [A_2115] :
      ( k1_relat_1(k2_funct_1(A_2115)) = k2_relat_1(A_2115)
      | ~ v2_funct_1(A_2115)
      | ~ v1_funct_1(A_2115)
      | ~ v1_relat_1(A_2115) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_17685,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17565,c_17673])).

tff(c_17689,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10092,c_76,c_70,c_17685])).

tff(c_16981,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16])).

tff(c_17934,plain,(
    ! [A_2141,B_2142,C_2143] :
      ( k2_relset_1(A_2141,B_2142,C_2143) = k2_relat_1(C_2143)
      | ~ m1_subset_1(C_2143,k1_zfmisc_1(k2_zfmisc_1(A_2141,B_2142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17944,plain,(
    ! [A_2141,B_2142] : k2_relset_1(A_2141,B_2142,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16981,c_17934])).

tff(c_17960,plain,(
    ! [A_2144,B_2145] : k2_relset_1(A_2144,B_2145,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17689,c_17944])).

tff(c_17480,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17475,c_17475,c_68])).

tff(c_17964,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_17960,c_17480])).

tff(c_17717,plain,(
    ! [A_2117,B_2118,C_2119] :
      ( k1_relset_1(A_2117,B_2118,C_2119) = k1_relat_1(C_2119)
      | ~ m1_subset_1(C_2119,k1_zfmisc_1(k2_zfmisc_1(A_2117,B_2118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17735,plain,(
    ! [A_2117,B_2118] : k1_relset_1(A_2117,B_2118,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16981,c_17717])).

tff(c_17972,plain,(
    ! [A_2117,B_2118] : k1_relset_1(A_2117,B_2118,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17964,c_17735])).

tff(c_80,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_18066,plain,(
    ! [C_2153,B_2154] :
      ( v1_funct_2(C_2153,'#skF_3',B_2154)
      | k1_relset_1('#skF_3',B_2154,C_2153) != '#skF_3'
      | ~ m1_subset_1(C_2153,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_16969,c_16969,c_16969,c_80])).

tff(c_18069,plain,(
    ! [B_2154] :
      ( v1_funct_2('#skF_3','#skF_3',B_2154)
      | k1_relset_1('#skF_3',B_2154,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_16981,c_18066])).

tff(c_18075,plain,(
    ! [B_2154] : v1_funct_2('#skF_3','#skF_3',B_2154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17972,c_18069])).

tff(c_17479,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17475,c_10056])).

tff(c_17617,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17565,c_17479])).

tff(c_18080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18075,c_17617])).

tff(c_18081,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17474])).

tff(c_18082,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17474])).

tff(c_18105,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18081,c_18082])).

tff(c_18334,plain,(
    ! [A_2167] :
      ( v1_funct_2('#skF_1',A_2167,'#skF_1')
      | A_2167 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18081,c_18081,c_18081,c_16977])).

tff(c_18147,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18081,c_18081,c_16980])).

tff(c_18239,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18147,c_18081,c_17426])).

tff(c_18095,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18081,c_10056])).

tff(c_18275,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18239,c_18095])).

tff(c_18337,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18334,c_18275])).

tff(c_18341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18105,c_18337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.65/5.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.01/5.47  
% 14.01/5.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.01/5.47  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.01/5.47  
% 14.01/5.47  %Foreground sorts:
% 14.01/5.47  
% 14.01/5.47  
% 14.01/5.47  %Background operators:
% 14.01/5.47  
% 14.01/5.47  
% 14.01/5.47  %Foreground operators:
% 14.01/5.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.01/5.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.01/5.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.01/5.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.01/5.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.01/5.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.01/5.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.01/5.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.01/5.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.01/5.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.01/5.47  tff('#skF_2', type, '#skF_2': $i).
% 14.01/5.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.01/5.47  tff('#skF_3', type, '#skF_3': $i).
% 14.01/5.47  tff('#skF_1', type, '#skF_1': $i).
% 14.01/5.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.01/5.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.01/5.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.01/5.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.01/5.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.01/5.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.01/5.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.01/5.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.01/5.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.01/5.47  
% 14.28/5.53  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 14.28/5.53  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.28/5.53  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.28/5.53  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 14.28/5.53  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.28/5.53  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.28/5.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.28/5.53  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.28/5.53  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.28/5.53  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 14.28/5.53  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.28/5.53  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.28/5.53  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 14.28/5.53  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 14.28/5.53  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 14.28/5.53  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 14.28/5.53  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_10067, plain, (![C_1591, A_1592, B_1593]: (v1_relat_1(C_1591) | ~m1_subset_1(C_1591, k1_zfmisc_1(k2_zfmisc_1(A_1592, B_1593))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.28/5.53  tff(c_10092, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_10067])).
% 14.28/5.53  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_10519, plain, (![A_1648, B_1649, C_1650]: (k2_relset_1(A_1648, B_1649, C_1650)=k2_relat_1(C_1650) | ~m1_subset_1(C_1650, k1_zfmisc_1(k2_zfmisc_1(A_1648, B_1649))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_10535, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_10519])).
% 14.28/5.53  tff(c_10551, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10535])).
% 14.28/5.53  tff(c_32, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.28/5.53  tff(c_189, plain, (![A_46]: (v1_funct_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.28/5.53  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_172, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 14.28/5.53  tff(c_192, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_172])).
% 14.28/5.53  tff(c_195, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_192])).
% 14.28/5.53  tff(c_230, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.28/5.53  tff(c_240, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_230])).
% 14.28/5.53  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_240])).
% 14.28/5.53  tff(c_255, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 14.28/5.53  tff(c_275, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_255])).
% 14.28/5.53  tff(c_284, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_275])).
% 14.28/5.53  tff(c_312, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.28/5.53  tff(c_333, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_312])).
% 14.28/5.53  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.28/5.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.28/5.53  tff(c_545, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_568, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_545])).
% 14.28/5.53  tff(c_2763, plain, (![B_273, A_274, C_275]: (k1_xboole_0=B_273 | k1_relset_1(A_274, B_273, C_275)=A_274 | ~v1_funct_2(C_275, A_274, B_273) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_2779, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_2763])).
% 14.28/5.53  tff(c_2796, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_568, c_2779])).
% 14.28/5.53  tff(c_2800, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2796])).
% 14.28/5.53  tff(c_1236, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_1252, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_1236])).
% 14.28/5.53  tff(c_1272, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_568, c_1252])).
% 14.28/5.53  tff(c_1276, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1272])).
% 14.28/5.53  tff(c_30, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_28, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.28/5.53  tff(c_256, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 14.28/5.53  tff(c_506, plain, (![A_96]: (k2_relat_1(k2_funct_1(A_96))=k1_relat_1(A_96) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_62, plain, (![A_33]: (v1_funct_2(A_33, k1_relat_1(A_33), k2_relat_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_2030, plain, (![A_233]: (v1_funct_2(k2_funct_1(A_233), k1_relat_1(k2_funct_1(A_233)), k1_relat_1(A_233)) | ~v1_funct_1(k2_funct_1(A_233)) | ~v1_relat_1(k2_funct_1(A_233)) | ~v2_funct_1(A_233) | ~v1_funct_1(A_233) | ~v1_relat_1(A_233))), inference(superposition, [status(thm), theory('equality')], [c_506, c_62])).
% 14.28/5.53  tff(c_2033, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1276, c_2030])).
% 14.28/5.53  tff(c_2044, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_256, c_2033])).
% 14.28/5.53  tff(c_2047, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2044])).
% 14.28/5.53  tff(c_2050, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2047])).
% 14.28/5.53  tff(c_2054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_2050])).
% 14.28/5.53  tff(c_2056, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2044])).
% 14.28/5.53  tff(c_632, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_645, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_632])).
% 14.28/5.53  tff(c_660, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_645])).
% 14.28/5.53  tff(c_574, plain, (![A_103]: (m1_subset_1(A_103, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_103), k2_relat_1(A_103)))) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.28/5.53  tff(c_1390, plain, (![A_188]: (r1_tarski(A_188, k2_zfmisc_1(k1_relat_1(A_188), k2_relat_1(A_188))) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(resolution, [status(thm)], [c_574, c_18])).
% 14.28/5.53  tff(c_2103, plain, (![A_239]: (r1_tarski(k2_funct_1(A_239), k2_zfmisc_1(k2_relat_1(A_239), k2_relat_1(k2_funct_1(A_239)))) | ~v1_funct_1(k2_funct_1(A_239)) | ~v1_relat_1(k2_funct_1(A_239)) | ~v2_funct_1(A_239) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1390])).
% 14.28/5.53  tff(c_2129, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_660, c_2103])).
% 14.28/5.53  tff(c_2147, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_2056, c_256, c_2129])).
% 14.28/5.53  tff(c_2173, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2147])).
% 14.28/5.53  tff(c_2191, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_1276, c_2173])).
% 14.28/5.53  tff(c_2193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_2191])).
% 14.28/5.53  tff(c_2194, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1272])).
% 14.28/5.53  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.28/5.53  tff(c_120, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.28/5.53  tff(c_128, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_120])).
% 14.28/5.53  tff(c_2221, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2194, c_128])).
% 14.28/5.53  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.28/5.53  tff(c_2225, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2194, c_2194, c_12])).
% 14.28/5.53  tff(c_60, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_665, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_660, c_60])).
% 14.28/5.53  tff(c_672, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_665])).
% 14.28/5.53  tff(c_709, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_672, c_18])).
% 14.28/5.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.28/5.53  tff(c_737, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_709, c_2])).
% 14.28/5.53  tff(c_1079, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_737])).
% 14.28/5.53  tff(c_2389, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2225, c_1079])).
% 14.28/5.53  tff(c_2399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2221, c_2389])).
% 14.28/5.53  tff(c_2400, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_737])).
% 14.28/5.53  tff(c_2803, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2800, c_2400])).
% 14.28/5.53  tff(c_127, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_120])).
% 14.28/5.53  tff(c_296, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.28/5.53  tff(c_306, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_127, c_296])).
% 14.28/5.53  tff(c_339, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_306])).
% 14.28/5.53  tff(c_2830, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_339])).
% 14.28/5.53  tff(c_2835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2830])).
% 14.28/5.53  tff(c_2836, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2796])).
% 14.28/5.53  tff(c_2866, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2836, c_128])).
% 14.28/5.53  tff(c_2870, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2836, c_2836, c_12])).
% 14.28/5.53  tff(c_3042, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2870, c_339])).
% 14.28/5.53  tff(c_3047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2866, c_3042])).
% 14.28/5.53  tff(c_3048, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_306])).
% 14.28/5.53  tff(c_3051, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3048, c_72])).
% 14.28/5.53  tff(c_3380, plain, (![A_317, B_318, C_319]: (k1_relset_1(A_317, B_318, C_319)=k1_relat_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_3555, plain, (![C_331]: (k1_relset_1('#skF_1', '#skF_2', C_331)=k1_relat_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_3380])).
% 14.28/5.53  tff(c_3567, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3051, c_3555])).
% 14.28/5.53  tff(c_5331, plain, (![B_456, A_457, C_458]: (k1_xboole_0=B_456 | k1_relset_1(A_457, B_456, C_458)=A_457 | ~v1_funct_2(C_458, A_457, B_456) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_457, B_456))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_5340, plain, (![C_458]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_458)='#skF_1' | ~v1_funct_2(C_458, '#skF_1', '#skF_2') | ~m1_subset_1(C_458, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_5331])).
% 14.28/5.53  tff(c_5402, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5340])).
% 14.28/5.53  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.28/5.53  tff(c_3058, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3048, c_10])).
% 14.28/5.53  tff(c_3112, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3058])).
% 14.28/5.53  tff(c_5425, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_3112])).
% 14.28/5.53  tff(c_5570, plain, (![A_467]: (k2_zfmisc_1(A_467, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_5402, c_12])).
% 14.28/5.53  tff(c_4073, plain, (![B_381, C_382, A_383]: (k1_xboole_0=B_381 | v1_funct_2(C_382, A_383, B_381) | k1_relset_1(A_383, B_381, C_382)!=A_383 | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_381))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_4082, plain, (![C_382]: (k1_xboole_0='#skF_2' | v1_funct_2(C_382, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_382)!='#skF_1' | ~m1_subset_1(C_382, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_4073])).
% 14.28/5.53  tff(c_4146, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4082])).
% 14.28/5.53  tff(c_4176, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4146, c_128])).
% 14.28/5.53  tff(c_4180, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4146, c_4146, c_12])).
% 14.28/5.53  tff(c_3332, plain, (![A_311, B_312, C_313]: (k2_relset_1(A_311, B_312, C_313)=k2_relat_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_3438, plain, (![C_325]: (k2_relset_1('#skF_1', '#skF_2', C_325)=k2_relat_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_3332])).
% 14.28/5.53  tff(c_3441, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3051, c_3438])).
% 14.28/5.53  tff(c_3451, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3441])).
% 14.28/5.53  tff(c_3270, plain, (![A_308]: (m1_subset_1(A_308, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_308), k2_relat_1(A_308)))) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_3293, plain, (![A_308]: (r1_tarski(A_308, k2_zfmisc_1(k1_relat_1(A_308), k2_relat_1(A_308))) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(resolution, [status(thm)], [c_3270, c_18])).
% 14.28/5.53  tff(c_3458, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3451, c_3293])).
% 14.28/5.53  tff(c_3468, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_3458])).
% 14.28/5.53  tff(c_3487, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_3468, c_2])).
% 14.28/5.53  tff(c_3649, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3487])).
% 14.28/5.53  tff(c_4386, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4180, c_3649])).
% 14.28/5.53  tff(c_4392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4176, c_4386])).
% 14.28/5.53  tff(c_4394, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4082])).
% 14.28/5.53  tff(c_4396, plain, (![B_394, A_395, C_396]: (k1_xboole_0=B_394 | k1_relset_1(A_395, B_394, C_396)=A_395 | ~v1_funct_2(C_396, A_395, B_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_4405, plain, (![C_396]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_396)='#skF_1' | ~v1_funct_2(C_396, '#skF_1', '#skF_2') | ~m1_subset_1(C_396, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3048, c_4396])).
% 14.28/5.53  tff(c_4577, plain, (![C_408]: (k1_relset_1('#skF_1', '#skF_2', C_408)='#skF_1' | ~v1_funct_2(C_408, '#skF_1', '#skF_2') | ~m1_subset_1(C_408, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4394, c_4405])).
% 14.28/5.53  tff(c_4580, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3051, c_4577])).
% 14.28/5.53  tff(c_4591, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3567, c_4580])).
% 14.28/5.53  tff(c_4596, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4591, c_3649])).
% 14.28/5.53  tff(c_4606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3048, c_4596])).
% 14.28/5.53  tff(c_4607, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_3487])).
% 14.28/5.53  tff(c_5592, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5570, c_4607])).
% 14.28/5.53  tff(c_5634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5425, c_5592])).
% 14.28/5.53  tff(c_5893, plain, (![C_489]: (k1_relset_1('#skF_1', '#skF_2', C_489)='#skF_1' | ~v1_funct_2(C_489, '#skF_1', '#skF_2') | ~m1_subset_1(C_489, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_5340])).
% 14.28/5.53  tff(c_5896, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3051, c_5893])).
% 14.28/5.53  tff(c_5907, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3567, c_5896])).
% 14.28/5.53  tff(c_3256, plain, (![A_307]: (k1_relat_1(k2_funct_1(A_307))=k2_relat_1(A_307) | ~v2_funct_1(A_307) | ~v1_funct_1(A_307) | ~v1_relat_1(A_307))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_6356, plain, (![A_512]: (v1_funct_2(k2_funct_1(A_512), k2_relat_1(A_512), k2_relat_1(k2_funct_1(A_512))) | ~v1_funct_1(k2_funct_1(A_512)) | ~v1_relat_1(k2_funct_1(A_512)) | ~v2_funct_1(A_512) | ~v1_funct_1(A_512) | ~v1_relat_1(A_512))), inference(superposition, [status(thm), theory('equality')], [c_3256, c_62])).
% 14.28/5.53  tff(c_6359, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3451, c_6356])).
% 14.28/5.53  tff(c_6367, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_256, c_6359])).
% 14.28/5.53  tff(c_6368, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6367])).
% 14.28/5.53  tff(c_6371, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_6368])).
% 14.28/5.53  tff(c_6375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_6371])).
% 14.28/5.53  tff(c_6377, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6367])).
% 14.28/5.53  tff(c_3294, plain, (![A_309]: (r1_tarski(A_309, k2_zfmisc_1(k1_relat_1(A_309), k2_relat_1(A_309))) | ~v1_funct_1(A_309) | ~v1_relat_1(A_309))), inference(resolution, [status(thm)], [c_3270, c_18])).
% 14.28/5.53  tff(c_6497, plain, (![A_523]: (r1_tarski(k2_funct_1(A_523), k2_zfmisc_1(k2_relat_1(A_523), k2_relat_1(k2_funct_1(A_523)))) | ~v1_funct_1(k2_funct_1(A_523)) | ~v1_relat_1(k2_funct_1(A_523)) | ~v2_funct_1(A_523) | ~v1_funct_1(A_523) | ~v1_relat_1(A_523))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3294])).
% 14.28/5.53  tff(c_6523, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3451, c_6497])).
% 14.28/5.53  tff(c_6541, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_6377, c_256, c_6523])).
% 14.28/5.53  tff(c_6567, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_6541])).
% 14.28/5.53  tff(c_6585, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_5907, c_6567])).
% 14.28/5.53  tff(c_6587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_6585])).
% 14.28/5.53  tff(c_6589, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3058])).
% 14.28/5.53  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.28/5.53  tff(c_6612, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_6589, c_14])).
% 14.28/5.53  tff(c_6588, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3058])).
% 14.28/5.53  tff(c_6710, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_6589, c_6588])).
% 14.28/5.53  tff(c_6711, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_6710])).
% 14.28/5.53  tff(c_6713, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_284])).
% 14.28/5.53  tff(c_6718, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6612, c_6713])).
% 14.28/5.53  tff(c_6614, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_16])).
% 14.28/5.53  tff(c_6828, plain, (![A_546, B_547, C_548]: (k2_relset_1(A_546, B_547, C_548)=k2_relat_1(C_548) | ~m1_subset_1(C_548, k1_zfmisc_1(k2_zfmisc_1(A_546, B_547))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_6849, plain, (![A_549, B_550]: (k2_relset_1(A_549, B_550, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6614, c_6828])).
% 14.28/5.53  tff(c_6715, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_6711, c_68])).
% 14.28/5.53  tff(c_6853, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6849, c_6715])).
% 14.28/5.53  tff(c_6759, plain, (![A_535]: (k1_relat_1(k2_funct_1(A_535))=k2_relat_1(A_535) | ~v2_funct_1(A_535) | ~v1_funct_1(A_535) | ~v1_relat_1(A_535))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_8142, plain, (![A_1428]: (v1_funct_2(k2_funct_1(A_1428), k2_relat_1(A_1428), k2_relat_1(k2_funct_1(A_1428))) | ~v1_funct_1(k2_funct_1(A_1428)) | ~v1_relat_1(k2_funct_1(A_1428)) | ~v2_funct_1(A_1428) | ~v1_funct_1(A_1428) | ~v1_relat_1(A_1428))), inference(superposition, [status(thm), theory('equality')], [c_6759, c_62])).
% 14.28/5.53  tff(c_8145, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6853, c_8142])).
% 14.28/5.53  tff(c_8153, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_256, c_8145])).
% 14.28/5.53  tff(c_8154, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8153])).
% 14.28/5.53  tff(c_8157, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_8154])).
% 14.28/5.53  tff(c_8161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_8157])).
% 14.28/5.53  tff(c_8163, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8153])).
% 14.28/5.53  tff(c_6879, plain, (![A_553]: (m1_subset_1(A_553, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_553), k2_relat_1(A_553)))) | ~v1_funct_1(A_553) | ~v1_relat_1(A_553))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_7686, plain, (![A_1391]: (r1_tarski(A_1391, k2_zfmisc_1(k1_relat_1(A_1391), k2_relat_1(A_1391))) | ~v1_funct_1(A_1391) | ~v1_relat_1(A_1391))), inference(resolution, [status(thm)], [c_6879, c_18])).
% 14.28/5.53  tff(c_8408, plain, (![A_1445]: (r1_tarski(k2_funct_1(A_1445), k2_zfmisc_1(k2_relat_1(A_1445), k2_relat_1(k2_funct_1(A_1445)))) | ~v1_funct_1(k2_funct_1(A_1445)) | ~v1_relat_1(k2_funct_1(A_1445)) | ~v2_funct_1(A_1445) | ~v1_funct_1(A_1445) | ~v1_relat_1(A_1445))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7686])).
% 14.28/5.53  tff(c_8434, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6853, c_8408])).
% 14.28/5.53  tff(c_8452, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_76, c_70, c_8163, c_256, c_6612, c_8434])).
% 14.28/5.53  tff(c_8454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6718, c_8452])).
% 14.28/5.53  tff(c_8455, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_6710])).
% 14.28/5.53  tff(c_6613, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_6589, c_12])).
% 14.28/5.53  tff(c_8459, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_8455, c_6613])).
% 14.28/5.53  tff(c_8468, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_275])).
% 14.28/5.53  tff(c_8695, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8459, c_8468])).
% 14.28/5.53  tff(c_8466, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_333])).
% 14.28/5.53  tff(c_8473, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_76])).
% 14.28/5.53  tff(c_8472, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_70])).
% 14.28/5.53  tff(c_136, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.28/5.53  tff(c_143, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_136])).
% 14.28/5.53  tff(c_152, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_18])).
% 14.28/5.53  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.28/5.53  tff(c_156, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_8])).
% 14.28/5.53  tff(c_6608, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_6589, c_156])).
% 14.28/5.53  tff(c_8463, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_8455, c_6608])).
% 14.28/5.53  tff(c_8458, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_6614])).
% 14.28/5.53  tff(c_8615, plain, (![A_1453, B_1454, C_1455]: (k1_relset_1(A_1453, B_1454, C_1455)=k1_relat_1(C_1455) | ~m1_subset_1(C_1455, k1_zfmisc_1(k2_zfmisc_1(A_1453, B_1454))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_8633, plain, (![A_1453, B_1454]: (k1_relset_1(A_1453, B_1454, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_8458, c_8615])).
% 14.28/5.53  tff(c_56, plain, (![A_32]: (v1_partfun1(k6_partfun1(A_32), A_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.28/5.53  tff(c_58, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.28/5.53  tff(c_8773, plain, (![C_1472, A_1473, B_1474]: (v1_funct_2(C_1472, A_1473, B_1474) | ~v1_partfun1(C_1472, A_1473) | ~v1_funct_1(C_1472) | ~m1_subset_1(C_1472, k1_zfmisc_1(k2_zfmisc_1(A_1473, B_1474))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.28/5.53  tff(c_8793, plain, (![A_32]: (v1_funct_2(k6_partfun1(A_32), A_32, A_32) | ~v1_partfun1(k6_partfun1(A_32), A_32) | ~v1_funct_1(k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_58, c_8773])).
% 14.28/5.53  tff(c_8801, plain, (![A_32]: (v1_funct_2(k6_partfun1(A_32), A_32, A_32) | ~v1_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8793])).
% 14.28/5.53  tff(c_8464, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_6589])).
% 14.28/5.53  tff(c_52, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_79, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52])).
% 14.28/5.53  tff(c_8924, plain, (![B_1490, C_1491]: (k1_relset_1('#skF_1', B_1490, C_1491)='#skF_1' | ~v1_funct_2(C_1491, '#skF_1', B_1490) | ~m1_subset_1(C_1491, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8464, c_8464, c_8464, c_8464, c_79])).
% 14.28/5.53  tff(c_8929, plain, (k1_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'))='#skF_1' | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_8801, c_8924])).
% 14.28/5.53  tff(c_8943, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8473, c_8463, c_8458, c_8463, c_8633, c_8463, c_8929])).
% 14.28/5.53  tff(c_8469, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_256])).
% 14.28/5.53  tff(c_8479, plain, (![A_1446]: (k2_relat_1(k2_funct_1(A_1446))=k1_relat_1(A_1446) | ~v2_funct_1(A_1446) | ~v1_funct_1(A_1446) | ~v1_relat_1(A_1446))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_9635, plain, (![A_1565]: (v1_funct_2(k2_funct_1(A_1565), k1_relat_1(k2_funct_1(A_1565)), k1_relat_1(A_1565)) | ~v1_funct_1(k2_funct_1(A_1565)) | ~v1_relat_1(k2_funct_1(A_1565)) | ~v2_funct_1(A_1565) | ~v1_funct_1(A_1565) | ~v1_relat_1(A_1565))), inference(superposition, [status(thm), theory('equality')], [c_8479, c_62])).
% 14.28/5.53  tff(c_9638, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8943, c_9635])).
% 14.28/5.53  tff(c_9646, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8466, c_8473, c_8472, c_8469, c_9638])).
% 14.28/5.53  tff(c_9647, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_9646])).
% 14.28/5.53  tff(c_9650, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_9647])).
% 14.28/5.53  tff(c_9654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8466, c_8473, c_9650])).
% 14.28/5.53  tff(c_9656, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_9646])).
% 14.28/5.53  tff(c_8659, plain, (![A_1461, B_1462, C_1463]: (k2_relset_1(A_1461, B_1462, C_1463)=k2_relat_1(C_1463) | ~m1_subset_1(C_1463, k1_zfmisc_1(k2_zfmisc_1(A_1461, B_1462))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_8708, plain, (![A_1467, B_1468]: (k2_relset_1(A_1467, B_1468, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_8458, c_8659])).
% 14.28/5.53  tff(c_8470, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8455, c_68])).
% 14.28/5.53  tff(c_8712, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_8708, c_8470])).
% 14.28/5.53  tff(c_8729, plain, (![A_1469]: (m1_subset_1(A_1469, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1469), k2_relat_1(A_1469)))) | ~v1_funct_1(A_1469) | ~v1_relat_1(A_1469))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.28/5.53  tff(c_9957, plain, (![A_1588]: (m1_subset_1(k2_funct_1(A_1588), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1588), k2_relat_1(k2_funct_1(A_1588))))) | ~v1_funct_1(k2_funct_1(A_1588)) | ~v1_relat_1(k2_funct_1(A_1588)) | ~v2_funct_1(A_1588) | ~v1_funct_1(A_1588) | ~v1_relat_1(A_1588))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8729])).
% 14.28/5.53  tff(c_9986, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1'))))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8712, c_9957])).
% 14.28/5.53  tff(c_10005, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_8466, c_8473, c_8472, c_9656, c_8469, c_9986])).
% 14.28/5.53  tff(c_10034, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_1')))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_10005])).
% 14.28/5.53  tff(c_10053, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8466, c_8473, c_8472, c_8459, c_8943, c_10034])).
% 14.28/5.53  tff(c_10055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8695, c_10053])).
% 14.28/5.53  tff(c_10056, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_255])).
% 14.28/5.53  tff(c_10057, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_255])).
% 14.28/5.53  tff(c_10359, plain, (![A_1630, B_1631, C_1632]: (k1_relset_1(A_1630, B_1631, C_1632)=k1_relat_1(C_1632) | ~m1_subset_1(C_1632, k1_zfmisc_1(k2_zfmisc_1(A_1630, B_1631))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_10383, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10057, c_10359])).
% 14.28/5.53  tff(c_11348, plain, (![B_1718, C_1719, A_1720]: (k1_xboole_0=B_1718 | v1_funct_2(C_1719, A_1720, B_1718) | k1_relset_1(A_1720, B_1718, C_1719)!=A_1720 | ~m1_subset_1(C_1719, k1_zfmisc_1(k2_zfmisc_1(A_1720, B_1718))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_11354, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_10057, c_11348])).
% 14.28/5.53  tff(c_11377, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10383, c_11354])).
% 14.28/5.53  tff(c_11378, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10056, c_11377])).
% 14.28/5.53  tff(c_11388, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_11378])).
% 14.28/5.53  tff(c_11391, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_11388])).
% 14.28/5.53  tff(c_11394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10092, c_76, c_70, c_10551, c_11391])).
% 14.28/5.53  tff(c_11395, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_11378])).
% 14.28/5.53  tff(c_11424, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_11395, c_128])).
% 14.28/5.53  tff(c_11427, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11395, c_11395, c_14])).
% 14.28/5.53  tff(c_10134, plain, (![B_1599, A_1600]: (B_1599=A_1600 | ~r1_tarski(B_1599, A_1600) | ~r1_tarski(A_1600, B_1599))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.28/5.53  tff(c_10147, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_127, c_10134])).
% 14.28/5.53  tff(c_10191, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_10147])).
% 14.28/5.53  tff(c_11546, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11427, c_10191])).
% 14.28/5.53  tff(c_11551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11424, c_11546])).
% 14.28/5.53  tff(c_11552, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_10147])).
% 14.28/5.53  tff(c_11555, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11552, c_72])).
% 14.28/5.53  tff(c_13553, plain, (![A_1863, B_1864, C_1865]: (k2_relset_1(A_1863, B_1864, C_1865)=k2_relat_1(C_1865) | ~m1_subset_1(C_1865, k1_zfmisc_1(k2_zfmisc_1(A_1863, B_1864))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_13665, plain, (![C_1877]: (k2_relset_1('#skF_1', '#skF_2', C_1877)=k2_relat_1(C_1877) | ~m1_subset_1(C_1877, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11552, c_13553])).
% 14.28/5.53  tff(c_13668, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11555, c_13665])).
% 14.28/5.53  tff(c_13678, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_13668])).
% 14.28/5.53  tff(c_15344, plain, (![B_1992, C_1993, A_1994]: (k1_xboole_0=B_1992 | v1_funct_2(C_1993, A_1994, B_1992) | k1_relset_1(A_1994, B_1992, C_1993)!=A_1994 | ~m1_subset_1(C_1993, k1_zfmisc_1(k2_zfmisc_1(A_1994, B_1992))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_15356, plain, (![C_1993]: (k1_xboole_0='#skF_2' | v1_funct_2(C_1993, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_1993)!='#skF_1' | ~m1_subset_1(C_1993, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11552, c_15344])).
% 14.28/5.53  tff(c_15434, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_15356])).
% 14.28/5.53  tff(c_11806, plain, (![A_1748, B_1749, C_1750]: (k2_relset_1(A_1748, B_1749, C_1750)=k2_relat_1(C_1750) | ~m1_subset_1(C_1750, k1_zfmisc_1(k2_zfmisc_1(A_1748, B_1749))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_11879, plain, (![C_1758]: (k2_relset_1('#skF_1', '#skF_2', C_1758)=k2_relat_1(C_1758) | ~m1_subset_1(C_1758, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11552, c_11806])).
% 14.28/5.53  tff(c_11882, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11555, c_11879])).
% 14.28/5.53  tff(c_11892, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_11882])).
% 14.28/5.53  tff(c_11957, plain, (![A_1759, B_1760, C_1761]: (k1_relset_1(A_1759, B_1760, C_1761)=k1_relat_1(C_1761) | ~m1_subset_1(C_1761, k1_zfmisc_1(k2_zfmisc_1(A_1759, B_1760))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_11989, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10057, c_11957])).
% 14.28/5.53  tff(c_13187, plain, (![B_1854, C_1855, A_1856]: (k1_xboole_0=B_1854 | v1_funct_2(C_1855, A_1856, B_1854) | k1_relset_1(A_1856, B_1854, C_1855)!=A_1856 | ~m1_subset_1(C_1855, k1_zfmisc_1(k2_zfmisc_1(A_1856, B_1854))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_13199, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_10057, c_13187])).
% 14.28/5.53  tff(c_13224, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11989, c_13199])).
% 14.28/5.53  tff(c_13225, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10056, c_13224])).
% 14.28/5.53  tff(c_13232, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_13225])).
% 14.28/5.53  tff(c_13235, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_13232])).
% 14.28/5.53  tff(c_13238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10092, c_76, c_70, c_11892, c_13235])).
% 14.28/5.53  tff(c_13239, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_13225])).
% 14.28/5.53  tff(c_13272, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13239, c_128])).
% 14.28/5.53  tff(c_13276, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13239, c_13239, c_12])).
% 14.28/5.53  tff(c_10066, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10057, c_18])).
% 14.28/5.53  tff(c_10145, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10066, c_10134])).
% 14.28/5.53  tff(c_11761, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10145])).
% 14.28/5.53  tff(c_13435, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13276, c_11761])).
% 14.28/5.53  tff(c_13441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13272, c_13435])).
% 14.28/5.53  tff(c_13442, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_10145])).
% 14.28/5.53  tff(c_13455, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13442, c_10])).
% 14.28/5.53  tff(c_13514, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13455])).
% 14.28/5.53  tff(c_15454, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15434, c_13514])).
% 14.28/5.53  tff(c_15467, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15434, c_15434, c_14])).
% 14.28/5.53  tff(c_15617, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15467, c_13442])).
% 14.28/5.53  tff(c_15619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15454, c_15617])).
% 14.28/5.53  tff(c_15621, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_15356])).
% 14.28/5.53  tff(c_13604, plain, (![A_1869, B_1870, C_1871]: (k1_relset_1(A_1869, B_1870, C_1871)=k1_relat_1(C_1871) | ~m1_subset_1(C_1871, k1_zfmisc_1(k2_zfmisc_1(A_1869, B_1870))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_13634, plain, (![A_1869, B_1870]: (k1_relset_1(A_1869, B_1870, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_13604])).
% 14.28/5.53  tff(c_48, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_13837, plain, (![C_1890, B_1891]: (v1_funct_2(C_1890, k1_xboole_0, B_1891) | k1_relset_1(k1_xboole_0, B_1891, C_1890)!=k1_xboole_0 | ~m1_subset_1(C_1890, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 14.28/5.53  tff(c_13843, plain, (![B_1891]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1891) | k1_relset_1(k1_xboole_0, B_1891, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_13837])).
% 14.28/5.53  tff(c_13846, plain, (![B_1891]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1891) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13634, c_13843])).
% 14.28/5.53  tff(c_13847, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13846])).
% 14.28/5.53  tff(c_167, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_56])).
% 14.28/5.53  tff(c_10089, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10057, c_10067])).
% 14.28/5.53  tff(c_11625, plain, (![B_1728, A_1729]: (v1_funct_1(B_1728) | ~m1_subset_1(B_1728, k1_zfmisc_1(A_1729)) | ~v1_funct_1(A_1729) | ~v1_relat_1(A_1729))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.28/5.53  tff(c_11651, plain, (![A_6]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_11625])).
% 14.28/5.53  tff(c_11654, plain, (![A_1732]: (~v1_funct_1(A_1732) | ~v1_relat_1(A_1732))), inference(splitLeft, [status(thm)], [c_11651])).
% 14.28/5.53  tff(c_11663, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10089, c_11654])).
% 14.28/5.53  tff(c_11675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_11663])).
% 14.28/5.53  tff(c_11676, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11651])).
% 14.28/5.53  tff(c_14093, plain, (![C_1916, A_1917, B_1918]: (v1_funct_2(C_1916, A_1917, B_1918) | ~v1_partfun1(C_1916, A_1917) | ~v1_funct_1(C_1916) | ~m1_subset_1(C_1916, k1_zfmisc_1(k2_zfmisc_1(A_1917, B_1918))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.28/5.53  tff(c_14122, plain, (![A_1917, B_1918]: (v1_funct_2(k1_xboole_0, A_1917, B_1918) | ~v1_partfun1(k1_xboole_0, A_1917) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_14093])).
% 14.28/5.53  tff(c_14134, plain, (![A_1919, B_1920]: (v1_funct_2(k1_xboole_0, A_1919, B_1920) | ~v1_partfun1(k1_xboole_0, A_1919))), inference(demodulation, [status(thm), theory('equality')], [c_11676, c_14122])).
% 14.28/5.53  tff(c_14137, plain, (![B_1920]: (k1_relset_1(k1_xboole_0, B_1920, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_14134, c_79])).
% 14.28/5.53  tff(c_14143, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_167, c_16, c_13634, c_14137])).
% 14.28/5.53  tff(c_14145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13847, c_14143])).
% 14.28/5.53  tff(c_14147, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_13846])).
% 14.28/5.53  tff(c_14148, plain, (![A_1869, B_1870]: (k1_relset_1(A_1869, B_1870, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14147, c_13634])).
% 14.28/5.53  tff(c_15373, plain, (![B_1992, A_1994]: (k1_xboole_0=B_1992 | v1_funct_2(k1_xboole_0, A_1994, B_1992) | k1_relset_1(A_1994, B_1992, k1_xboole_0)!=A_1994)), inference(resolution, [status(thm)], [c_16, c_15344])).
% 14.28/5.53  tff(c_15380, plain, (![B_1992, A_1994]: (k1_xboole_0=B_1992 | v1_funct_2(k1_xboole_0, A_1994, B_1992) | k1_xboole_0!=A_1994)), inference(demodulation, [status(thm), theory('equality')], [c_14148, c_15373])).
% 14.28/5.53  tff(c_15661, plain, (![B_2005, A_2006, C_2007]: (k1_xboole_0=B_2005 | k1_relset_1(A_2006, B_2005, C_2007)=A_2006 | ~v1_funct_2(C_2007, A_2006, B_2005) | ~m1_subset_1(C_2007, k1_zfmisc_1(k2_zfmisc_1(A_2006, B_2005))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_15673, plain, (![C_2007]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_2007)='#skF_1' | ~v1_funct_2(C_2007, '#skF_1', '#skF_2') | ~m1_subset_1(C_2007, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11552, c_15661])).
% 14.28/5.53  tff(c_15870, plain, (![C_2023]: (k1_relset_1('#skF_1', '#skF_2', C_2023)='#skF_1' | ~v1_funct_2(C_2023, '#skF_1', '#skF_2') | ~m1_subset_1(C_2023, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_15621, c_15673])).
% 14.28/5.53  tff(c_15881, plain, (k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_15870])).
% 14.28/5.53  tff(c_15887, plain, (k1_xboole_0='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14148, c_15881])).
% 14.28/5.53  tff(c_15935, plain, (~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_15887])).
% 14.28/5.53  tff(c_15976, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_1'), inference(resolution, [status(thm)], [c_15380, c_15935])).
% 14.28/5.53  tff(c_15985, plain, (k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_15621, c_15976])).
% 14.28/5.53  tff(c_14306, plain, (![A_1938, B_1939, A_1940]: (k1_relset_1(A_1938, B_1939, A_1940)=k1_relat_1(A_1940) | ~r1_tarski(A_1940, k2_zfmisc_1(A_1938, B_1939)))), inference(resolution, [status(thm)], [c_20, c_13604])).
% 14.28/5.53  tff(c_14343, plain, (![A_1938, B_1939]: (k1_relset_1(A_1938, B_1939, k2_zfmisc_1(A_1938, B_1939))=k1_relat_1(k2_zfmisc_1(A_1938, B_1939)))), inference(resolution, [status(thm)], [c_6, c_14306])).
% 14.28/5.53  tff(c_16183, plain, (![B_2039, A_2040, A_2041]: (k1_xboole_0=B_2039 | v1_funct_2(A_2040, A_2041, B_2039) | k1_relset_1(A_2041, B_2039, A_2040)!=A_2041 | ~r1_tarski(A_2040, k2_zfmisc_1(A_2041, B_2039)))), inference(resolution, [status(thm)], [c_20, c_15344])).
% 14.28/5.53  tff(c_16209, plain, (![B_2039, A_2041]: (k1_xboole_0=B_2039 | v1_funct_2(k2_zfmisc_1(A_2041, B_2039), A_2041, B_2039) | k1_relset_1(A_2041, B_2039, k2_zfmisc_1(A_2041, B_2039))!=A_2041)), inference(resolution, [status(thm)], [c_6, c_16183])).
% 14.28/5.53  tff(c_16257, plain, (![B_2045, A_2046]: (k1_xboole_0=B_2045 | v1_funct_2(k2_zfmisc_1(A_2046, B_2045), A_2046, B_2045) | k1_relat_1(k2_zfmisc_1(A_2046, B_2045))!=A_2046)), inference(demodulation, [status(thm), theory('equality')], [c_14343, c_16209])).
% 14.28/5.53  tff(c_16270, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13442, c_16257])).
% 14.28/5.53  tff(c_16291, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13442, c_16270])).
% 14.28/5.53  tff(c_16292, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10056, c_15985, c_16291])).
% 14.28/5.53  tff(c_16301, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_16292])).
% 14.28/5.53  tff(c_16304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10092, c_76, c_70, c_13678, c_16301])).
% 14.28/5.53  tff(c_16305, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_15887])).
% 14.28/5.53  tff(c_11564, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11552, c_10])).
% 14.28/5.53  tff(c_11607, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_11564])).
% 14.28/5.53  tff(c_16339, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16305, c_11607])).
% 14.28/5.53  tff(c_16349, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16305, c_16305, c_14])).
% 14.28/5.53  tff(c_16642, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16349, c_11552])).
% 14.28/5.53  tff(c_16644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16339, c_16642])).
% 14.28/5.53  tff(c_16645, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_13455])).
% 14.28/5.53  tff(c_16680, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_16645])).
% 14.28/5.53  tff(c_16685, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16680, c_11607])).
% 14.28/5.53  tff(c_16695, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16680, c_16680, c_14])).
% 14.28/5.53  tff(c_16803, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16695, c_11552])).
% 14.28/5.53  tff(c_16805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16685, c_16803])).
% 14.28/5.53  tff(c_16806, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16645])).
% 14.28/5.53  tff(c_16811, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16806, c_11607])).
% 14.28/5.53  tff(c_16927, plain, (![A_2066]: (k2_zfmisc_1(A_2066, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16806, c_16806, c_12])).
% 14.28/5.53  tff(c_16942, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16927, c_11552])).
% 14.28/5.53  tff(c_16967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16811, c_16942])).
% 14.28/5.53  tff(c_16969, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11564])).
% 14.28/5.53  tff(c_16979, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_14])).
% 14.28/5.53  tff(c_16968, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_11564])).
% 14.28/5.53  tff(c_17474, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_16968])).
% 14.28/5.53  tff(c_17475, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_17474])).
% 14.28/5.53  tff(c_16976, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_128])).
% 14.28/5.53  tff(c_17021, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_16968])).
% 14.28/5.53  tff(c_17022, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_17021])).
% 14.28/5.53  tff(c_16987, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10145])).
% 14.28/5.53  tff(c_17145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16976, c_16979, c_17022, c_16987])).
% 14.28/5.53  tff(c_17146, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_17021])).
% 14.28/5.53  tff(c_17147, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_17021])).
% 14.28/5.53  tff(c_17171, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_17147])).
% 14.28/5.53  tff(c_44, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.28/5.53  tff(c_78, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_44])).
% 14.28/5.53  tff(c_16977, plain, (![A_29]: (v1_funct_2('#skF_3', A_29, '#skF_3') | A_29='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_16969, c_78])).
% 14.28/5.53  tff(c_17418, plain, (![A_2089]: (v1_funct_2('#skF_1', A_2089, '#skF_1') | A_2089='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_17146, c_17146, c_16977])).
% 14.28/5.53  tff(c_16980, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_12])).
% 14.28/5.53  tff(c_17210, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_17146, c_16980])).
% 14.28/5.53  tff(c_17160, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_10057])).
% 14.28/5.53  tff(c_17337, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17210, c_17160])).
% 14.28/5.53  tff(c_17350, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_17337, c_18])).
% 14.28/5.53  tff(c_16978, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_8])).
% 14.28/5.53  tff(c_17307, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_17146, c_16978])).
% 14.28/5.53  tff(c_17361, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_17350, c_17307])).
% 14.28/5.53  tff(c_17161, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17146, c_10056])).
% 14.28/5.53  tff(c_17367, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17361, c_17161])).
% 14.28/5.53  tff(c_17421, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_17418, c_17367])).
% 14.28/5.53  tff(c_17425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17171, c_17421])).
% 14.28/5.53  tff(c_17426, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_10145])).
% 14.28/5.53  tff(c_17565, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16979, c_17475, c_17426])).
% 14.28/5.53  tff(c_17673, plain, (![A_2115]: (k1_relat_1(k2_funct_1(A_2115))=k2_relat_1(A_2115) | ~v2_funct_1(A_2115) | ~v1_funct_1(A_2115) | ~v1_relat_1(A_2115))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.28/5.53  tff(c_17685, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17565, c_17673])).
% 14.28/5.53  tff(c_17689, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10092, c_76, c_70, c_17685])).
% 14.28/5.53  tff(c_16981, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16])).
% 14.28/5.53  tff(c_17934, plain, (![A_2141, B_2142, C_2143]: (k2_relset_1(A_2141, B_2142, C_2143)=k2_relat_1(C_2143) | ~m1_subset_1(C_2143, k1_zfmisc_1(k2_zfmisc_1(A_2141, B_2142))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.28/5.53  tff(c_17944, plain, (![A_2141, B_2142]: (k2_relset_1(A_2141, B_2142, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16981, c_17934])).
% 14.28/5.53  tff(c_17960, plain, (![A_2144, B_2145]: (k2_relset_1(A_2144, B_2145, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17689, c_17944])).
% 14.28/5.53  tff(c_17480, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17475, c_17475, c_68])).
% 14.28/5.53  tff(c_17964, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_17960, c_17480])).
% 14.28/5.53  tff(c_17717, plain, (![A_2117, B_2118, C_2119]: (k1_relset_1(A_2117, B_2118, C_2119)=k1_relat_1(C_2119) | ~m1_subset_1(C_2119, k1_zfmisc_1(k2_zfmisc_1(A_2117, B_2118))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.28/5.53  tff(c_17735, plain, (![A_2117, B_2118]: (k1_relset_1(A_2117, B_2118, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16981, c_17717])).
% 14.28/5.53  tff(c_17972, plain, (![A_2117, B_2118]: (k1_relset_1(A_2117, B_2118, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17964, c_17735])).
% 14.28/5.53  tff(c_80, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 14.28/5.53  tff(c_18066, plain, (![C_2153, B_2154]: (v1_funct_2(C_2153, '#skF_3', B_2154) | k1_relset_1('#skF_3', B_2154, C_2153)!='#skF_3' | ~m1_subset_1(C_2153, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_16969, c_16969, c_16969, c_80])).
% 14.28/5.53  tff(c_18069, plain, (![B_2154]: (v1_funct_2('#skF_3', '#skF_3', B_2154) | k1_relset_1('#skF_3', B_2154, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_16981, c_18066])).
% 14.28/5.53  tff(c_18075, plain, (![B_2154]: (v1_funct_2('#skF_3', '#skF_3', B_2154))), inference(demodulation, [status(thm), theory('equality')], [c_17972, c_18069])).
% 14.28/5.53  tff(c_17479, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17475, c_10056])).
% 14.28/5.53  tff(c_17617, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17565, c_17479])).
% 14.28/5.53  tff(c_18080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18075, c_17617])).
% 14.28/5.53  tff(c_18081, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_17474])).
% 14.28/5.53  tff(c_18082, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_17474])).
% 14.28/5.53  tff(c_18105, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18081, c_18082])).
% 14.28/5.53  tff(c_18334, plain, (![A_2167]: (v1_funct_2('#skF_1', A_2167, '#skF_1') | A_2167='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18081, c_18081, c_18081, c_16977])).
% 14.28/5.53  tff(c_18147, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18081, c_18081, c_16980])).
% 14.28/5.53  tff(c_18239, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18147, c_18081, c_17426])).
% 14.28/5.53  tff(c_18095, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18081, c_10056])).
% 14.28/5.53  tff(c_18275, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18239, c_18095])).
% 14.28/5.53  tff(c_18337, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_18334, c_18275])).
% 14.28/5.53  tff(c_18341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18105, c_18337])).
% 14.28/5.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.28/5.53  
% 14.28/5.53  Inference rules
% 14.28/5.53  ----------------------
% 14.28/5.53  #Ref     : 0
% 14.28/5.53  #Sup     : 3748
% 14.28/5.53  #Fact    : 0
% 14.28/5.53  #Define  : 0
% 14.28/5.53  #Split   : 68
% 14.28/5.53  #Chain   : 0
% 14.28/5.53  #Close   : 0
% 14.28/5.53  
% 14.28/5.53  Ordering : KBO
% 14.28/5.53  
% 14.28/5.53  Simplification rules
% 14.28/5.53  ----------------------
% 14.28/5.53  #Subsume      : 486
% 14.28/5.53  #Demod        : 5280
% 14.28/5.53  #Tautology    : 2079
% 14.28/5.53  #SimpNegUnit  : 81
% 14.28/5.53  #BackRed      : 634
% 14.28/5.53  
% 14.28/5.53  #Partial instantiations: 56
% 14.28/5.53  #Strategies tried      : 1
% 14.28/5.53  
% 14.28/5.53  Timing (in seconds)
% 14.28/5.53  ----------------------
% 14.28/5.54  Preprocessing        : 0.56
% 14.28/5.54  Parsing              : 0.29
% 14.28/5.54  CNF conversion       : 0.04
% 14.28/5.54  Main loop            : 3.97
% 14.28/5.54  Inferencing          : 1.42
% 14.28/5.54  Reduction            : 1.44
% 14.28/5.54  Demodulation         : 1.04
% 14.28/5.54  BG Simplification    : 0.12
% 14.28/5.54  Subsumption          : 0.67
% 14.28/5.54  Abstraction          : 0.14
% 14.28/5.54  MUC search           : 0.00
% 14.28/5.54  Cooper               : 0.00
% 14.28/5.54  Total                : 4.73
% 14.28/5.54  Index Insertion      : 0.00
% 14.28/5.54  Index Deletion       : 0.00
% 14.28/5.54  Index Matching       : 0.00
% 14.28/5.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
