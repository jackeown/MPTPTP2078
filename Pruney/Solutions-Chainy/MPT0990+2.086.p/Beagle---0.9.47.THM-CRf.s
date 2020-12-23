%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:08 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :  166 (1048 expanded)
%              Number of leaves         :   44 ( 398 expanded)
%              Depth                    :   17
%              Number of atoms          :  427 (4626 expanded)
%              Number of equality atoms :  115 (1448 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_240,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_198,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_139,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_214,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_115,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_182,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_156,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_117,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_129,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_117])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_208,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_221,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_208])).

tff(c_3874,plain,(
    ! [C_204,A_205,B_206] :
      ( v1_funct_1(k2_funct_1(C_204))
      | k2_relset_1(A_205,B_206,C_204) != B_206
      | ~ v2_funct_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_2(C_204,A_205,B_206)
      | ~ v1_funct_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_3883,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3874])).

tff(c_3891,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_221,c_3883])).

tff(c_3892,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3891])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_117])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_214,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_208])).

tff(c_220,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_214])).

tff(c_193,plain,(
    ! [A_75] :
      ( k1_relat_1(k2_funct_1(A_75)) = k2_relat_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_5928,plain,(
    ! [A_278] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_278)),k2_funct_1(A_278)) = k2_funct_1(A_278)
      | ~ v1_relat_1(k2_funct_1(A_278))
      | ~ v2_funct_1(A_278)
      | ~ v1_funct_1(A_278)
      | ~ v1_relat_1(A_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_91])).

tff(c_5964,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_5928])).

tff(c_5992,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_88,c_72,c_5964])).

tff(c_5993,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5992])).

tff(c_6013,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5993])).

tff(c_6017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_88,c_6013])).

tff(c_6019,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5992])).

tff(c_3880,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3874])).

tff(c_3888,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_72,c_76,c_3880])).

tff(c_12,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_6393,plain,(
    ! [B_298,C_299,A_300] :
      ( k6_partfun1(B_298) = k5_relat_1(k2_funct_1(C_299),C_299)
      | k1_xboole_0 = B_298
      | ~ v2_funct_1(C_299)
      | k2_relset_1(A_300,B_298,C_299) != B_298
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_300,B_298)))
      | ~ v1_funct_2(C_299,A_300,B_298)
      | ~ v1_funct_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_6399,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_6393])).

tff(c_6407,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_6399])).

tff(c_6408,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6407])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v2_funct_1(k5_relat_1(A_12,B_13))
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6425,plain,
    ( v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6408,c_18])).

tff(c_6438,plain,
    ( v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6019,c_3888,c_128,c_88,c_72,c_6425])).

tff(c_6442,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6438])).

tff(c_6445,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_6442])).

tff(c_6449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_88,c_72,c_6445])).

tff(c_6451,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6438])).

tff(c_6590,plain,(
    ! [A_304,C_305,B_306] :
      ( k6_partfun1(A_304) = k5_relat_1(C_305,k2_funct_1(C_305))
      | k1_xboole_0 = B_306
      | ~ v2_funct_1(C_305)
      | k2_relset_1(A_304,B_306,C_305) != B_306
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_306)))
      | ~ v1_funct_2(C_305,A_304,B_306)
      | ~ v1_funct_1(C_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_6596,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_6590])).

tff(c_6604,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_6596])).

tff(c_6605,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6604])).

tff(c_6634,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6605,c_18])).

tff(c_6655,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_88,c_72,c_6019,c_3888,c_6451,c_6634])).

tff(c_2825,plain,(
    ! [B_177,E_173,D_176,A_172,C_174,F_175] :
      ( k1_partfun1(A_172,B_177,C_174,D_176,E_173,F_175) = k5_relat_1(E_173,F_175)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_174,D_176)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_177)))
      | ~ v1_funct_1(E_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2831,plain,(
    ! [A_172,B_177,E_173] :
      ( k1_partfun1(A_172,B_177,'#skF_2','#skF_1',E_173,'#skF_4') = k5_relat_1(E_173,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_177)))
      | ~ v1_funct_1(E_173) ) ),
    inference(resolution,[status(thm)],[c_78,c_2825])).

tff(c_3065,plain,(
    ! [A_185,B_186,E_187] :
      ( k1_partfun1(A_185,B_186,'#skF_2','#skF_1',E_187,'#skF_4') = k5_relat_1(E_187,'#skF_4')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(E_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2831])).

tff(c_3074,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3065])).

tff(c_3082,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3074])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_89,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_604,plain,(
    ! [D_93,C_94,A_95,B_96] :
      ( D_93 = C_94
      | ~ r2_relset_1(A_95,B_96,C_94,D_93)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_612,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_604])).

tff(c_627,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_612])).

tff(c_654,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_3087,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_654])).

tff(c_3470,plain,(
    ! [E_197,D_196,C_195,F_194,B_198,A_199] :
      ( m1_subset_1(k1_partfun1(A_199,B_198,C_195,D_196,E_197,F_194),k1_zfmisc_1(k2_zfmisc_1(A_199,D_196)))
      | ~ m1_subset_1(F_194,k1_zfmisc_1(k2_zfmisc_1(C_195,D_196)))
      | ~ v1_funct_1(F_194)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3510,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_3470])).

tff(c_3533,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_3510])).

tff(c_3535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3087,c_3533])).

tff(c_3536,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_7372,plain,(
    ! [A_326,D_328,C_329,B_325,E_327] :
      ( k1_xboole_0 = C_329
      | v2_funct_1(E_327)
      | k2_relset_1(A_326,B_325,D_328) != B_325
      | ~ v2_funct_1(k1_partfun1(A_326,B_325,B_325,C_329,D_328,E_327))
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(B_325,C_329)))
      | ~ v1_funct_2(E_327,B_325,C_329)
      | ~ v1_funct_1(E_327)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325)))
      | ~ v1_funct_2(D_328,A_326,B_325)
      | ~ v1_funct_1(D_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_7376,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3536,c_7372])).

tff(c_7381,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_6655,c_76,c_7376])).

tff(c_7383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3892,c_70,c_7381])).

tff(c_7385,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3891])).

tff(c_7384,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3891])).

tff(c_7386,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7384])).

tff(c_167,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_174,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_89,c_167])).

tff(c_10613,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( k2_relset_1(A_443,B_444,C_445) = B_444
      | ~ r2_relset_1(B_444,B_444,k1_partfun1(B_444,A_443,A_443,B_444,D_446,C_445),k6_partfun1(B_444))
      | ~ m1_subset_1(D_446,k1_zfmisc_1(k2_zfmisc_1(B_444,A_443)))
      | ~ v1_funct_2(D_446,B_444,A_443)
      | ~ v1_funct_1(D_446)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_2(C_445,A_443,B_444)
      | ~ v1_funct_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10619,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3536,c_10613])).

tff(c_10623,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_174,c_221,c_10619])).

tff(c_10625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7386,c_10623])).

tff(c_10627,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7384])).

tff(c_10628,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10627,c_221])).

tff(c_11879,plain,(
    ! [A_495,C_496,B_497] :
      ( k6_partfun1(A_495) = k5_relat_1(C_496,k2_funct_1(C_496))
      | k1_xboole_0 = B_497
      | ~ v2_funct_1(C_496)
      | k2_relset_1(A_495,B_497,C_496) != B_497
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_495,B_497)))
      | ~ v1_funct_2(C_496,A_495,B_497)
      | ~ v1_funct_1(C_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_11887,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_11879])).

tff(c_11897,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_10628,c_7385,c_11887])).

tff(c_11898,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_11897])).

tff(c_127,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_89,c_117])).

tff(c_280,plain,(
    ! [A_84,B_85,C_86] :
      ( k5_relat_1(k5_relat_1(A_84,B_85),C_86) = k5_relat_1(A_84,k5_relat_1(B_85,C_86))
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_308,plain,(
    ! [A_8,C_86] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_86)) = k5_relat_1(A_8,C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_280])).

tff(c_323,plain,(
    ! [A_8,C_86] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_86)) = k5_relat_1(A_8,C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_308])).

tff(c_11950,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11898,c_323])).

tff(c_11966,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_11898,c_11950])).

tff(c_12250,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11966])).

tff(c_12253,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_12250])).

tff(c_12257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_82,c_12253])).

tff(c_12259,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11966])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_partfun1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_225,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_90])).

tff(c_229,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_225])).

tff(c_13555,plain,(
    ! [A_533] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_533)),k2_funct_1(A_533)) = k2_funct_1(A_533)
      | ~ v1_relat_1(k2_funct_1(A_533))
      | ~ v2_funct_1(A_533)
      | ~ v1_funct_1(A_533)
      | ~ v1_relat_1(A_533) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_91])).

tff(c_13595,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10627,c_13555])).

tff(c_13629,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_82,c_7385,c_12259,c_13595])).

tff(c_11594,plain,(
    ! [F_481,E_479,B_483,D_482,C_480,A_478] :
      ( k1_partfun1(A_478,B_483,C_480,D_482,E_479,F_481) = k5_relat_1(E_479,F_481)
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_zfmisc_1(C_480,D_482)))
      | ~ v1_funct_1(F_481)
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(A_478,B_483)))
      | ~ v1_funct_1(E_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_11602,plain,(
    ! [A_478,B_483,E_479] :
      ( k1_partfun1(A_478,B_483,'#skF_2','#skF_1',E_479,'#skF_4') = k5_relat_1(E_479,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(A_478,B_483)))
      | ~ v1_funct_1(E_479) ) ),
    inference(resolution,[status(thm)],[c_78,c_11594])).

tff(c_12820,plain,(
    ! [A_522,B_523,E_524] :
      ( k1_partfun1(A_522,B_523,'#skF_2','#skF_1',E_524,'#skF_4') = k5_relat_1(E_524,'#skF_4')
      | ~ m1_subset_1(E_524,k1_zfmisc_1(k2_zfmisc_1(A_522,B_523)))
      | ~ v1_funct_1(E_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_11602])).

tff(c_12838,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_12820])).

tff(c_12853,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3536,c_12838])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12872,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12853,c_2])).

tff(c_12890,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_129,c_12872])).

tff(c_13635,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13629,c_12890])).

tff(c_13657,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12259,c_229,c_11898,c_13635])).

tff(c_26,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13706,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13657,c_26])).

tff(c_13729,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_82,c_7385,c_13706])).

tff(c_13731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_13729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.43  
% 9.66/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.44  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.66/3.44  
% 9.66/3.44  %Foreground sorts:
% 9.66/3.44  
% 9.66/3.44  
% 9.66/3.44  %Background operators:
% 9.66/3.44  
% 9.66/3.44  
% 9.66/3.44  %Foreground operators:
% 9.66/3.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.66/3.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.66/3.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.66/3.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.66/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.66/3.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.66/3.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.66/3.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.66/3.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.66/3.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.66/3.44  tff('#skF_2', type, '#skF_2': $i).
% 9.66/3.44  tff('#skF_3', type, '#skF_3': $i).
% 9.66/3.44  tff('#skF_1', type, '#skF_1': $i).
% 9.66/3.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.66/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.66/3.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.66/3.44  tff('#skF_4', type, '#skF_4': $i).
% 9.66/3.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.66/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.66/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.44  
% 9.66/3.46  tff(f_240, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.66/3.46  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.66/3.46  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.66/3.46  tff(f_198, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.66/3.46  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.66/3.46  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.66/3.46  tff(f_139, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.66/3.46  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.66/3.46  tff(f_63, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 9.66/3.46  tff(f_214, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.66/3.46  tff(f_79, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 9.66/3.46  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.66/3.46  tff(f_115, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.66/3.46  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.66/3.46  tff(f_127, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.66/3.46  tff(f_182, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.66/3.46  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.66/3.46  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.66/3.46  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.66/3.46  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 9.66/3.46  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_117, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.66/3.46  tff(c_129, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_117])).
% 9.66/3.46  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_208, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.66/3.46  tff(c_221, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_208])).
% 9.66/3.46  tff(c_3874, plain, (![C_204, A_205, B_206]: (v1_funct_1(k2_funct_1(C_204)) | k2_relset_1(A_205, B_206, C_204)!=B_206 | ~v2_funct_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_2(C_204, A_205, B_206) | ~v1_funct_1(C_204))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.66/3.46  tff(c_3883, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_3874])).
% 9.66/3.46  tff(c_3891, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_221, c_3883])).
% 9.66/3.46  tff(c_3892, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3891])).
% 9.66/3.46  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_117])).
% 9.66/3.46  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.66/3.46  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_214, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_208])).
% 9.66/3.46  tff(c_220, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_214])).
% 9.66/3.46  tff(c_193, plain, (![A_75]: (k1_relat_1(k2_funct_1(A_75))=k2_relat_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.66/3.46  tff(c_44, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.66/3.46  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.66/3.46  tff(c_91, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 9.66/3.46  tff(c_5928, plain, (![A_278]: (k5_relat_1(k6_partfun1(k2_relat_1(A_278)), k2_funct_1(A_278))=k2_funct_1(A_278) | ~v1_relat_1(k2_funct_1(A_278)) | ~v2_funct_1(A_278) | ~v1_funct_1(A_278) | ~v1_relat_1(A_278))), inference(superposition, [status(thm), theory('equality')], [c_193, c_91])).
% 9.66/3.46  tff(c_5964, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_220, c_5928])).
% 9.66/3.46  tff(c_5992, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_88, c_72, c_5964])).
% 9.66/3.46  tff(c_5993, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5992])).
% 9.66/3.46  tff(c_6013, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5993])).
% 9.66/3.46  tff(c_6017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_88, c_6013])).
% 9.66/3.46  tff(c_6019, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5992])).
% 9.66/3.46  tff(c_3880, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3874])).
% 9.66/3.46  tff(c_3888, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_72, c_76, c_3880])).
% 9.66/3.46  tff(c_12, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.66/3.46  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_6393, plain, (![B_298, C_299, A_300]: (k6_partfun1(B_298)=k5_relat_1(k2_funct_1(C_299), C_299) | k1_xboole_0=B_298 | ~v2_funct_1(C_299) | k2_relset_1(A_300, B_298, C_299)!=B_298 | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_300, B_298))) | ~v1_funct_2(C_299, A_300, B_298) | ~v1_funct_1(C_299))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.66/3.46  tff(c_6399, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_6393])).
% 9.66/3.46  tff(c_6407, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_6399])).
% 9.66/3.46  tff(c_6408, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_6407])).
% 9.66/3.46  tff(c_18, plain, (![A_12, B_13]: (v2_funct_1(k5_relat_1(A_12, B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.66/3.46  tff(c_6425, plain, (v2_funct_1(k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6408, c_18])).
% 9.66/3.46  tff(c_6438, plain, (v2_funct_1(k6_partfun1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6019, c_3888, c_128, c_88, c_72, c_6425])).
% 9.66/3.46  tff(c_6442, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6438])).
% 9.66/3.46  tff(c_6445, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_6442])).
% 9.66/3.46  tff(c_6449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_88, c_72, c_6445])).
% 9.66/3.46  tff(c_6451, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6438])).
% 9.66/3.46  tff(c_6590, plain, (![A_304, C_305, B_306]: (k6_partfun1(A_304)=k5_relat_1(C_305, k2_funct_1(C_305)) | k1_xboole_0=B_306 | ~v2_funct_1(C_305) | k2_relset_1(A_304, B_306, C_305)!=B_306 | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_306))) | ~v1_funct_2(C_305, A_304, B_306) | ~v1_funct_1(C_305))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.66/3.46  tff(c_6596, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_6590])).
% 9.66/3.46  tff(c_6604, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_6596])).
% 9.66/3.46  tff(c_6605, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_6604])).
% 9.66/3.46  tff(c_6634, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6605, c_18])).
% 9.66/3.46  tff(c_6655, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_88, c_72, c_6019, c_3888, c_6451, c_6634])).
% 9.66/3.46  tff(c_2825, plain, (![B_177, E_173, D_176, A_172, C_174, F_175]: (k1_partfun1(A_172, B_177, C_174, D_176, E_173, F_175)=k5_relat_1(E_173, F_175) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_174, D_176))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_177))) | ~v1_funct_1(E_173))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.66/3.46  tff(c_2831, plain, (![A_172, B_177, E_173]: (k1_partfun1(A_172, B_177, '#skF_2', '#skF_1', E_173, '#skF_4')=k5_relat_1(E_173, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_177))) | ~v1_funct_1(E_173))), inference(resolution, [status(thm)], [c_78, c_2825])).
% 9.66/3.46  tff(c_3065, plain, (![A_185, B_186, E_187]: (k1_partfun1(A_185, B_186, '#skF_2', '#skF_1', E_187, '#skF_4')=k5_relat_1(E_187, '#skF_4') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(E_187))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2831])).
% 9.66/3.46  tff(c_3074, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3065])).
% 9.66/3.46  tff(c_3082, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3074])).
% 9.66/3.46  tff(c_36, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.66/3.46  tff(c_89, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 9.66/3.46  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 9.66/3.46  tff(c_604, plain, (![D_93, C_94, A_95, B_96]: (D_93=C_94 | ~r2_relset_1(A_95, B_96, C_94, D_93) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.66/3.46  tff(c_612, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_604])).
% 9.66/3.46  tff(c_627, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_612])).
% 9.66/3.46  tff(c_654, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_627])).
% 9.66/3.46  tff(c_3087, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_654])).
% 9.66/3.46  tff(c_3470, plain, (![E_197, D_196, C_195, F_194, B_198, A_199]: (m1_subset_1(k1_partfun1(A_199, B_198, C_195, D_196, E_197, F_194), k1_zfmisc_1(k2_zfmisc_1(A_199, D_196))) | ~m1_subset_1(F_194, k1_zfmisc_1(k2_zfmisc_1(C_195, D_196))) | ~v1_funct_1(F_194) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.66/3.46  tff(c_3510, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3082, c_3470])).
% 9.66/3.46  tff(c_3533, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_3510])).
% 9.66/3.46  tff(c_3535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3087, c_3533])).
% 9.66/3.46  tff(c_3536, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_627])).
% 9.66/3.46  tff(c_7372, plain, (![A_326, D_328, C_329, B_325, E_327]: (k1_xboole_0=C_329 | v2_funct_1(E_327) | k2_relset_1(A_326, B_325, D_328)!=B_325 | ~v2_funct_1(k1_partfun1(A_326, B_325, B_325, C_329, D_328, E_327)) | ~m1_subset_1(E_327, k1_zfmisc_1(k2_zfmisc_1(B_325, C_329))) | ~v1_funct_2(E_327, B_325, C_329) | ~v1_funct_1(E_327) | ~m1_subset_1(D_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))) | ~v1_funct_2(D_328, A_326, B_325) | ~v1_funct_1(D_328))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.66/3.46  tff(c_7376, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3536, c_7372])).
% 9.66/3.46  tff(c_7381, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_6655, c_76, c_7376])).
% 9.66/3.46  tff(c_7383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3892, c_70, c_7381])).
% 9.66/3.46  tff(c_7385, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3891])).
% 9.66/3.46  tff(c_7384, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3891])).
% 9.66/3.46  tff(c_7386, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_7384])).
% 9.66/3.46  tff(c_167, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.66/3.46  tff(c_174, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_89, c_167])).
% 9.66/3.46  tff(c_10613, plain, (![A_443, B_444, C_445, D_446]: (k2_relset_1(A_443, B_444, C_445)=B_444 | ~r2_relset_1(B_444, B_444, k1_partfun1(B_444, A_443, A_443, B_444, D_446, C_445), k6_partfun1(B_444)) | ~m1_subset_1(D_446, k1_zfmisc_1(k2_zfmisc_1(B_444, A_443))) | ~v1_funct_2(D_446, B_444, A_443) | ~v1_funct_1(D_446) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_2(C_445, A_443, B_444) | ~v1_funct_1(C_445))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.66/3.46  tff(c_10619, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3536, c_10613])).
% 9.66/3.46  tff(c_10623, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_174, c_221, c_10619])).
% 9.66/3.46  tff(c_10625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7386, c_10623])).
% 9.66/3.46  tff(c_10627, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_7384])).
% 9.66/3.46  tff(c_10628, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10627, c_221])).
% 9.66/3.46  tff(c_11879, plain, (![A_495, C_496, B_497]: (k6_partfun1(A_495)=k5_relat_1(C_496, k2_funct_1(C_496)) | k1_xboole_0=B_497 | ~v2_funct_1(C_496) | k2_relset_1(A_495, B_497, C_496)!=B_497 | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_495, B_497))) | ~v1_funct_2(C_496, A_495, B_497) | ~v1_funct_1(C_496))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.66/3.46  tff(c_11887, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_11879])).
% 9.66/3.46  tff(c_11897, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_10628, c_7385, c_11887])).
% 9.66/3.46  tff(c_11898, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_11897])).
% 9.66/3.46  tff(c_127, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_89, c_117])).
% 9.66/3.46  tff(c_280, plain, (![A_84, B_85, C_86]: (k5_relat_1(k5_relat_1(A_84, B_85), C_86)=k5_relat_1(A_84, k5_relat_1(B_85, C_86)) | ~v1_relat_1(C_86) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.66/3.46  tff(c_308, plain, (![A_8, C_86]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_86))=k5_relat_1(A_8, C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(A_8) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_91, c_280])).
% 9.66/3.46  tff(c_323, plain, (![A_8, C_86]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_86))=k5_relat_1(A_8, C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_308])).
% 9.66/3.46  tff(c_11950, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11898, c_323])).
% 9.66/3.46  tff(c_11966, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_11898, c_11950])).
% 9.66/3.46  tff(c_12250, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11966])).
% 9.66/3.46  tff(c_12253, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_12250])).
% 9.66/3.46  tff(c_12257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_82, c_12253])).
% 9.66/3.46  tff(c_12259, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11966])).
% 9.66/3.46  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.66/3.46  tff(c_90, plain, (![A_9]: (k5_relat_1(A_9, k6_partfun1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 9.66/3.46  tff(c_225, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_220, c_90])).
% 9.66/3.46  tff(c_229, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_225])).
% 9.66/3.46  tff(c_13555, plain, (![A_533]: (k5_relat_1(k6_partfun1(k2_relat_1(A_533)), k2_funct_1(A_533))=k2_funct_1(A_533) | ~v1_relat_1(k2_funct_1(A_533)) | ~v2_funct_1(A_533) | ~v1_funct_1(A_533) | ~v1_relat_1(A_533))), inference(superposition, [status(thm), theory('equality')], [c_193, c_91])).
% 9.66/3.46  tff(c_13595, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10627, c_13555])).
% 9.66/3.46  tff(c_13629, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_82, c_7385, c_12259, c_13595])).
% 9.66/3.46  tff(c_11594, plain, (![F_481, E_479, B_483, D_482, C_480, A_478]: (k1_partfun1(A_478, B_483, C_480, D_482, E_479, F_481)=k5_relat_1(E_479, F_481) | ~m1_subset_1(F_481, k1_zfmisc_1(k2_zfmisc_1(C_480, D_482))) | ~v1_funct_1(F_481) | ~m1_subset_1(E_479, k1_zfmisc_1(k2_zfmisc_1(A_478, B_483))) | ~v1_funct_1(E_479))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.66/3.46  tff(c_11602, plain, (![A_478, B_483, E_479]: (k1_partfun1(A_478, B_483, '#skF_2', '#skF_1', E_479, '#skF_4')=k5_relat_1(E_479, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_479, k1_zfmisc_1(k2_zfmisc_1(A_478, B_483))) | ~v1_funct_1(E_479))), inference(resolution, [status(thm)], [c_78, c_11594])).
% 9.66/3.46  tff(c_12820, plain, (![A_522, B_523, E_524]: (k1_partfun1(A_522, B_523, '#skF_2', '#skF_1', E_524, '#skF_4')=k5_relat_1(E_524, '#skF_4') | ~m1_subset_1(E_524, k1_zfmisc_1(k2_zfmisc_1(A_522, B_523))) | ~v1_funct_1(E_524))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_11602])).
% 9.66/3.46  tff(c_12838, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_12820])).
% 9.66/3.46  tff(c_12853, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3536, c_12838])).
% 9.66/3.46  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.66/3.46  tff(c_12872, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12853, c_2])).
% 9.66/3.46  tff(c_12890, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_129, c_12872])).
% 9.66/3.46  tff(c_13635, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13629, c_12890])).
% 9.66/3.46  tff(c_13657, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12259, c_229, c_11898, c_13635])).
% 9.66/3.46  tff(c_26, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.66/3.46  tff(c_13706, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13657, c_26])).
% 9.66/3.46  tff(c_13729, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_82, c_7385, c_13706])).
% 9.66/3.46  tff(c_13731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_13729])).
% 9.66/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.46  
% 9.66/3.46  Inference rules
% 9.66/3.46  ----------------------
% 9.66/3.46  #Ref     : 0
% 9.66/3.46  #Sup     : 2968
% 9.66/3.46  #Fact    : 0
% 9.66/3.46  #Define  : 0
% 9.66/3.46  #Split   : 34
% 9.66/3.46  #Chain   : 0
% 9.66/3.46  #Close   : 0
% 9.66/3.46  
% 9.66/3.46  Ordering : KBO
% 9.66/3.46  
% 9.66/3.46  Simplification rules
% 9.66/3.46  ----------------------
% 9.66/3.46  #Subsume      : 122
% 9.66/3.46  #Demod        : 5332
% 9.66/3.46  #Tautology    : 1419
% 9.66/3.46  #SimpNegUnit  : 66
% 9.66/3.46  #BackRed      : 70
% 9.66/3.46  
% 9.66/3.46  #Partial instantiations: 0
% 9.66/3.46  #Strategies tried      : 1
% 9.66/3.46  
% 9.66/3.46  Timing (in seconds)
% 9.66/3.46  ----------------------
% 9.66/3.47  Preprocessing        : 0.40
% 9.66/3.47  Parsing              : 0.21
% 9.66/3.47  CNF conversion       : 0.03
% 9.66/3.47  Main loop            : 2.26
% 9.66/3.47  Inferencing          : 0.72
% 9.66/3.47  Reduction            : 0.94
% 9.66/3.47  Demodulation         : 0.72
% 9.66/3.47  BG Simplification    : 0.09
% 9.66/3.47  Subsumption          : 0.37
% 9.66/3.47  Abstraction          : 0.12
% 9.66/3.47  MUC search           : 0.00
% 9.66/3.47  Cooper               : 0.00
% 9.66/3.47  Total                : 2.72
% 9.66/3.47  Index Insertion      : 0.00
% 9.66/3.47  Index Deletion       : 0.00
% 9.66/3.47  Index Matching       : 0.00
% 9.66/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
