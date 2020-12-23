%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 9.44s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 953 expanded)
%              Number of leaves         :   45 ( 363 expanded)
%              Depth                    :   17
%              Number of atoms          :  403 (4250 expanded)
%              Number of equality atoms :  106 (1321 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_242,negated_conjecture,(
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

tff(f_200,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

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

tff(f_141,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_216,axiom,(
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

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_184,axiom,(
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

tff(f_158,axiom,(
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

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_119,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_131,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_119])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_210,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_223,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_210])).

tff(c_3302,plain,(
    ! [C_198,A_199,B_200] :
      ( v1_funct_1(k2_funct_1(C_198))
      | k2_relset_1(A_199,B_200,C_198) != B_200
      | ~ v2_funct_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_2(C_198,A_199,B_200)
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_3311,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_3302])).

tff(c_3319,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_223,c_3311])).

tff(c_3320,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3319])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_119])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_12,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_216,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_210])).

tff(c_222,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_216])).

tff(c_180,plain,(
    ! [A_75] :
      ( k1_relat_1(k2_funct_1(A_75)) = k2_relat_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_5242,plain,(
    ! [A_273] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_273)),k2_funct_1(A_273)) = k2_funct_1(A_273)
      | ~ v1_relat_1(k2_funct_1(A_273))
      | ~ v2_funct_1(A_273)
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_92])).

tff(c_5278,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_5242])).

tff(c_5306,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_5278])).

tff(c_5307,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5306])).

tff(c_5327,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5307])).

tff(c_5331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_5327])).

tff(c_5333,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5306])).

tff(c_3308,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_3302])).

tff(c_3316,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_74,c_78,c_3308])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_5725,plain,(
    ! [A_293,C_294,B_295] :
      ( k6_partfun1(A_293) = k5_relat_1(C_294,k2_funct_1(C_294))
      | k1_xboole_0 = B_295
      | ~ v2_funct_1(C_294)
      | k2_relset_1(A_293,B_295,C_294) != B_295
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_293,B_295)))
      | ~ v1_funct_2(C_294,A_293,B_295)
      | ~ v1_funct_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_5731,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_5725])).

tff(c_5739,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_5731])).

tff(c_5740,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5739])).

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

tff(c_5769,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5740,c_18])).

tff(c_5790,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_5333,c_3316,c_5769])).

tff(c_5794,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5790])).

tff(c_5797,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_5794])).

tff(c_5801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_90,c_74,c_5797])).

tff(c_5802,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5790])).

tff(c_2619,plain,(
    ! [C_170,D_172,E_169,B_173,F_171,A_168] :
      ( k1_partfun1(A_168,B_173,C_170,D_172,E_169,F_171) = k5_relat_1(E_169,F_171)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_170,D_172)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_173)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2627,plain,(
    ! [A_168,B_173,E_169] :
      ( k1_partfun1(A_168,B_173,'#skF_2','#skF_1',E_169,'#skF_4') = k5_relat_1(E_169,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_173)))
      | ~ v1_funct_1(E_169) ) ),
    inference(resolution,[status(thm)],[c_80,c_2619])).

tff(c_2849,plain,(
    ! [A_182,B_183,E_184] :
      ( k1_partfun1(A_182,B_183,'#skF_2','#skF_1',E_184,'#skF_4') = k5_relat_1(E_184,'#skF_4')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_1(E_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2627])).

tff(c_2858,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2849])).

tff(c_2866,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2858])).

tff(c_42,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_539,plain,(
    ! [D_92,C_93,A_94,B_95] :
      ( D_92 = C_93
      | ~ r2_relset_1(A_94,B_95,C_93,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_547,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_539])).

tff(c_562,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_547])).

tff(c_589,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_562])).

tff(c_2975,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_589])).

tff(c_2986,plain,(
    ! [D_188,A_190,E_193,B_189,F_191,C_192] :
      ( m1_subset_1(k1_partfun1(A_190,B_189,C_192,D_188,E_193,F_191),k1_zfmisc_1(k2_zfmisc_1(A_190,D_188)))
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(C_192,D_188)))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ v1_funct_1(E_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3023,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_2986])).

tff(c_3047,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_3023])).

tff(c_3054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2975,c_3047])).

tff(c_3055,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_562])).

tff(c_6504,plain,(
    ! [C_320,B_316,E_318,A_317,D_319] :
      ( k1_xboole_0 = C_320
      | v2_funct_1(E_318)
      | k2_relset_1(A_317,B_316,D_319) != B_316
      | ~ v2_funct_1(k1_partfun1(A_317,B_316,B_316,C_320,D_319,E_318))
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(B_316,C_320)))
      | ~ v1_funct_2(E_318,B_316,C_320)
      | ~ v1_funct_1(E_318)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316)))
      | ~ v1_funct_2(D_319,A_317,B_316)
      | ~ v1_funct_1(D_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_6508,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_6504])).

tff(c_6513,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_5802,c_78,c_6508])).

tff(c_6515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3320,c_72,c_6513])).

tff(c_6517,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3319])).

tff(c_6516,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3319])).

tff(c_6518,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6516])).

tff(c_169,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_176,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_42,c_169])).

tff(c_10121,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( k2_relset_1(A_447,B_448,C_449) = B_448
      | ~ r2_relset_1(B_448,B_448,k1_partfun1(B_448,A_447,A_447,B_448,D_450,C_449),k6_partfun1(B_448))
      | ~ m1_subset_1(D_450,k1_zfmisc_1(k2_zfmisc_1(B_448,A_447)))
      | ~ v1_funct_2(D_450,B_448,A_447)
      | ~ v1_funct_1(D_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_2(C_449,A_447,B_448)
      | ~ v1_funct_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_10127,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_10121])).

tff(c_10131,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_90,c_88,c_86,c_176,c_223,c_10127])).

tff(c_10133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6518,c_10131])).

tff(c_10135,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6516])).

tff(c_10136,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10135,c_223])).

tff(c_11264,plain,(
    ! [A_494,C_495,B_496] :
      ( k6_partfun1(A_494) = k5_relat_1(C_495,k2_funct_1(C_495))
      | k1_xboole_0 = B_496
      | ~ v2_funct_1(C_495)
      | k2_relset_1(A_494,B_496,C_495) != B_496
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_494,B_496)))
      | ~ v1_funct_2(C_495,A_494,B_496)
      | ~ v1_funct_1(C_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_11272,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_11264])).

tff(c_11282,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_10136,c_6517,c_11272])).

tff(c_11283,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11282])).

tff(c_129,plain,(
    ! [A_32] : v1_relat_1(k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_282,plain,(
    ! [A_85,B_86,C_87] :
      ( k5_relat_1(k5_relat_1(A_85,B_86),C_87) = k5_relat_1(A_85,k5_relat_1(B_86,C_87))
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_317,plain,(
    ! [A_8,C_87] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_87)) = k5_relat_1(A_8,C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_282])).

tff(c_329,plain,(
    ! [A_8,C_87] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_87)) = k5_relat_1(A_8,C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_317])).

tff(c_11327,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11283,c_329])).

tff(c_11342,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_11283,c_11327])).

tff(c_11381,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11342])).

tff(c_11457,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_11381])).

tff(c_11461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_11457])).

tff(c_11463,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11342])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_partfun1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_227,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_91])).

tff(c_231,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_227])).

tff(c_12830,plain,(
    ! [A_534] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_534)),k2_funct_1(A_534)) = k2_funct_1(A_534)
      | ~ v1_relat_1(k2_funct_1(A_534))
      | ~ v2_funct_1(A_534)
      | ~ v1_funct_1(A_534)
      | ~ v1_relat_1(A_534) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_92])).

tff(c_12862,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10135,c_12830])).

tff(c_12890,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_6517,c_11463,c_12862])).

tff(c_10752,plain,(
    ! [F_475,A_472,C_474,D_476,B_477,E_473] :
      ( k1_partfun1(A_472,B_477,C_474,D_476,E_473,F_475) = k5_relat_1(E_473,F_475)
      | ~ m1_subset_1(F_475,k1_zfmisc_1(k2_zfmisc_1(C_474,D_476)))
      | ~ v1_funct_1(F_475)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(A_472,B_477)))
      | ~ v1_funct_1(E_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10758,plain,(
    ! [A_472,B_477,E_473] :
      ( k1_partfun1(A_472,B_477,'#skF_2','#skF_1',E_473,'#skF_4') = k5_relat_1(E_473,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(A_472,B_477)))
      | ~ v1_funct_1(E_473) ) ),
    inference(resolution,[status(thm)],[c_80,c_10752])).

tff(c_11091,plain,(
    ! [A_488,B_489,E_490] :
      ( k1_partfun1(A_488,B_489,'#skF_2','#skF_1',E_490,'#skF_4') = k5_relat_1(E_490,'#skF_4')
      | ~ m1_subset_1(E_490,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489)))
      | ~ v1_funct_1(E_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10758])).

tff(c_11100,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_11091])).

tff(c_11108,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3055,c_11100])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11124,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11108,c_2])).

tff(c_11140,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_131,c_11124])).

tff(c_12896,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12890,c_11140])).

tff(c_12918,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11463,c_231,c_11283,c_12896])).

tff(c_26,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12958,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12918,c_26])).

tff(c_12979,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84,c_6517,c_12958])).

tff(c_12981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_12979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.44/3.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.34  
% 9.44/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.35  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.44/3.35  
% 9.44/3.35  %Foreground sorts:
% 9.44/3.35  
% 9.44/3.35  
% 9.44/3.35  %Background operators:
% 9.44/3.35  
% 9.44/3.35  
% 9.44/3.35  %Foreground operators:
% 9.44/3.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.44/3.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.44/3.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.44/3.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.44/3.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.44/3.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.44/3.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.44/3.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.44/3.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.44/3.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.44/3.35  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.44/3.35  tff('#skF_3', type, '#skF_3': $i).
% 9.44/3.35  tff('#skF_1', type, '#skF_1': $i).
% 9.44/3.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.44/3.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.44/3.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.44/3.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.44/3.35  tff('#skF_4', type, '#skF_4': $i).
% 9.44/3.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.44/3.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.44/3.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.35  
% 9.64/3.37  tff(f_242, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.64/3.37  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.64/3.37  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.64/3.37  tff(f_200, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.64/3.37  tff(f_63, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 9.64/3.37  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.64/3.37  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.64/3.37  tff(f_141, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.64/3.37  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.64/3.37  tff(f_216, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.64/3.37  tff(f_79, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 9.64/3.37  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.64/3.37  tff(f_129, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.64/3.37  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.64/3.37  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.64/3.37  tff(f_184, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.64/3.37  tff(f_158, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.64/3.37  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.64/3.37  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.64/3.37  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 9.64/3.37  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_119, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.64/3.37  tff(c_131, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_119])).
% 9.64/3.37  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_210, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.64/3.37  tff(c_223, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_210])).
% 9.64/3.37  tff(c_3302, plain, (![C_198, A_199, B_200]: (v1_funct_1(k2_funct_1(C_198)) | k2_relset_1(A_199, B_200, C_198)!=B_200 | ~v2_funct_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_2(C_198, A_199, B_200) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_200])).
% 9.64/3.37  tff(c_3311, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_3302])).
% 9.64/3.37  tff(c_3319, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_223, c_3311])).
% 9.64/3.37  tff(c_3320, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3319])).
% 9.64/3.37  tff(c_72, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_119])).
% 9.64/3.37  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_12, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.64/3.37  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.64/3.37  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_216, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_210])).
% 9.64/3.37  tff(c_222, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_216])).
% 9.64/3.37  tff(c_180, plain, (![A_75]: (k1_relat_1(k2_funct_1(A_75))=k2_relat_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.64/3.37  tff(c_46, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.37  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.64/3.37  tff(c_92, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 9.64/3.37  tff(c_5242, plain, (![A_273]: (k5_relat_1(k6_partfun1(k2_relat_1(A_273)), k2_funct_1(A_273))=k2_funct_1(A_273) | ~v1_relat_1(k2_funct_1(A_273)) | ~v2_funct_1(A_273) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(superposition, [status(thm), theory('equality')], [c_180, c_92])).
% 9.64/3.37  tff(c_5278, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_222, c_5242])).
% 9.64/3.37  tff(c_5306, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_5278])).
% 9.64/3.37  tff(c_5307, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5306])).
% 9.64/3.37  tff(c_5327, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5307])).
% 9.64/3.37  tff(c_5331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_5327])).
% 9.64/3.37  tff(c_5333, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5306])).
% 9.64/3.37  tff(c_3308, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_3302])).
% 9.64/3.37  tff(c_3316, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_74, c_78, c_3308])).
% 9.64/3.37  tff(c_70, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_5725, plain, (![A_293, C_294, B_295]: (k6_partfun1(A_293)=k5_relat_1(C_294, k2_funct_1(C_294)) | k1_xboole_0=B_295 | ~v2_funct_1(C_294) | k2_relset_1(A_293, B_295, C_294)!=B_295 | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_293, B_295))) | ~v1_funct_2(C_294, A_293, B_295) | ~v1_funct_1(C_294))), inference(cnfTransformation, [status(thm)], [f_216])).
% 9.64/3.37  tff(c_5731, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_5725])).
% 9.64/3.37  tff(c_5739, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_5731])).
% 9.64/3.37  tff(c_5740, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_70, c_5739])).
% 9.64/3.37  tff(c_18, plain, (![A_12, B_13]: (v2_funct_1(k5_relat_1(A_12, B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.64/3.37  tff(c_5769, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5740, c_18])).
% 9.64/3.37  tff(c_5790, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_5333, c_3316, c_5769])).
% 9.64/3.37  tff(c_5794, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5790])).
% 9.64/3.37  tff(c_5797, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_5794])).
% 9.64/3.37  tff(c_5801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_90, c_74, c_5797])).
% 9.64/3.37  tff(c_5802, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_5790])).
% 9.64/3.37  tff(c_2619, plain, (![C_170, D_172, E_169, B_173, F_171, A_168]: (k1_partfun1(A_168, B_173, C_170, D_172, E_169, F_171)=k5_relat_1(E_169, F_171) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_170, D_172))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_173))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.64/3.37  tff(c_2627, plain, (![A_168, B_173, E_169]: (k1_partfun1(A_168, B_173, '#skF_2', '#skF_1', E_169, '#skF_4')=k5_relat_1(E_169, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_173))) | ~v1_funct_1(E_169))), inference(resolution, [status(thm)], [c_80, c_2619])).
% 9.64/3.37  tff(c_2849, plain, (![A_182, B_183, E_184]: (k1_partfun1(A_182, B_183, '#skF_2', '#skF_1', E_184, '#skF_4')=k5_relat_1(E_184, '#skF_4') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_1(E_184))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2627])).
% 9.64/3.37  tff(c_2858, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2849])).
% 9.64/3.37  tff(c_2866, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2858])).
% 9.64/3.37  tff(c_42, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.64/3.37  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 9.64/3.37  tff(c_539, plain, (![D_92, C_93, A_94, B_95]: (D_92=C_93 | ~r2_relset_1(A_94, B_95, C_93, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.64/3.37  tff(c_547, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_539])).
% 9.64/3.37  tff(c_562, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_547])).
% 9.64/3.37  tff(c_589, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_562])).
% 9.64/3.37  tff(c_2975, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2866, c_589])).
% 9.64/3.37  tff(c_2986, plain, (![D_188, A_190, E_193, B_189, F_191, C_192]: (m1_subset_1(k1_partfun1(A_190, B_189, C_192, D_188, E_193, F_191), k1_zfmisc_1(k2_zfmisc_1(A_190, D_188))) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(C_192, D_188))) | ~v1_funct_1(F_191) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~v1_funct_1(E_193))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.64/3.37  tff(c_3023, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_2986])).
% 9.64/3.37  tff(c_3047, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_3023])).
% 9.64/3.37  tff(c_3054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2975, c_3047])).
% 9.64/3.37  tff(c_3055, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_562])).
% 9.64/3.37  tff(c_6504, plain, (![C_320, B_316, E_318, A_317, D_319]: (k1_xboole_0=C_320 | v2_funct_1(E_318) | k2_relset_1(A_317, B_316, D_319)!=B_316 | ~v2_funct_1(k1_partfun1(A_317, B_316, B_316, C_320, D_319, E_318)) | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(B_316, C_320))) | ~v1_funct_2(E_318, B_316, C_320) | ~v1_funct_1(E_318) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))) | ~v1_funct_2(D_319, A_317, B_316) | ~v1_funct_1(D_319))), inference(cnfTransformation, [status(thm)], [f_184])).
% 9.64/3.37  tff(c_6508, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3055, c_6504])).
% 9.64/3.37  tff(c_6513, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_5802, c_78, c_6508])).
% 9.64/3.37  tff(c_6515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3320, c_72, c_6513])).
% 9.64/3.37  tff(c_6517, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3319])).
% 9.64/3.37  tff(c_6516, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3319])).
% 9.64/3.37  tff(c_6518, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_6516])).
% 9.64/3.37  tff(c_169, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.64/3.37  tff(c_176, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_42, c_169])).
% 9.64/3.37  tff(c_10121, plain, (![A_447, B_448, C_449, D_450]: (k2_relset_1(A_447, B_448, C_449)=B_448 | ~r2_relset_1(B_448, B_448, k1_partfun1(B_448, A_447, A_447, B_448, D_450, C_449), k6_partfun1(B_448)) | ~m1_subset_1(D_450, k1_zfmisc_1(k2_zfmisc_1(B_448, A_447))) | ~v1_funct_2(D_450, B_448, A_447) | ~v1_funct_1(D_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_2(C_449, A_447, B_448) | ~v1_funct_1(C_449))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.64/3.37  tff(c_10127, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3055, c_10121])).
% 9.64/3.37  tff(c_10131, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_90, c_88, c_86, c_176, c_223, c_10127])).
% 9.64/3.37  tff(c_10133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6518, c_10131])).
% 9.64/3.37  tff(c_10135, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_6516])).
% 9.64/3.37  tff(c_10136, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10135, c_223])).
% 9.64/3.37  tff(c_11264, plain, (![A_494, C_495, B_496]: (k6_partfun1(A_494)=k5_relat_1(C_495, k2_funct_1(C_495)) | k1_xboole_0=B_496 | ~v2_funct_1(C_495) | k2_relset_1(A_494, B_496, C_495)!=B_496 | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_494, B_496))) | ~v1_funct_2(C_495, A_494, B_496) | ~v1_funct_1(C_495))), inference(cnfTransformation, [status(thm)], [f_216])).
% 9.64/3.37  tff(c_11272, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_11264])).
% 9.64/3.37  tff(c_11282, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_10136, c_6517, c_11272])).
% 9.64/3.37  tff(c_11283, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_11282])).
% 9.64/3.37  tff(c_129, plain, (![A_32]: (v1_relat_1(k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_42, c_119])).
% 9.64/3.37  tff(c_282, plain, (![A_85, B_86, C_87]: (k5_relat_1(k5_relat_1(A_85, B_86), C_87)=k5_relat_1(A_85, k5_relat_1(B_86, C_87)) | ~v1_relat_1(C_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.64/3.37  tff(c_317, plain, (![A_8, C_87]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_87))=k5_relat_1(A_8, C_87) | ~v1_relat_1(C_87) | ~v1_relat_1(A_8) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_92, c_282])).
% 9.64/3.37  tff(c_329, plain, (![A_8, C_87]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_87))=k5_relat_1(A_8, C_87) | ~v1_relat_1(C_87) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_317])).
% 9.64/3.37  tff(c_11327, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11283, c_329])).
% 9.64/3.37  tff(c_11342, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_11283, c_11327])).
% 9.64/3.37  tff(c_11381, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11342])).
% 9.64/3.37  tff(c_11457, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_11381])).
% 9.64/3.37  tff(c_11461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_11457])).
% 9.64/3.37  tff(c_11463, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11342])).
% 9.64/3.37  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.64/3.37  tff(c_91, plain, (![A_9]: (k5_relat_1(A_9, k6_partfun1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 9.64/3.37  tff(c_227, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_222, c_91])).
% 9.64/3.37  tff(c_231, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_227])).
% 9.64/3.37  tff(c_12830, plain, (![A_534]: (k5_relat_1(k6_partfun1(k2_relat_1(A_534)), k2_funct_1(A_534))=k2_funct_1(A_534) | ~v1_relat_1(k2_funct_1(A_534)) | ~v2_funct_1(A_534) | ~v1_funct_1(A_534) | ~v1_relat_1(A_534))), inference(superposition, [status(thm), theory('equality')], [c_180, c_92])).
% 9.64/3.37  tff(c_12862, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10135, c_12830])).
% 9.64/3.37  tff(c_12890, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_6517, c_11463, c_12862])).
% 9.64/3.37  tff(c_10752, plain, (![F_475, A_472, C_474, D_476, B_477, E_473]: (k1_partfun1(A_472, B_477, C_474, D_476, E_473, F_475)=k5_relat_1(E_473, F_475) | ~m1_subset_1(F_475, k1_zfmisc_1(k2_zfmisc_1(C_474, D_476))) | ~v1_funct_1(F_475) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(A_472, B_477))) | ~v1_funct_1(E_473))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.64/3.37  tff(c_10758, plain, (![A_472, B_477, E_473]: (k1_partfun1(A_472, B_477, '#skF_2', '#skF_1', E_473, '#skF_4')=k5_relat_1(E_473, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(A_472, B_477))) | ~v1_funct_1(E_473))), inference(resolution, [status(thm)], [c_80, c_10752])).
% 9.64/3.37  tff(c_11091, plain, (![A_488, B_489, E_490]: (k1_partfun1(A_488, B_489, '#skF_2', '#skF_1', E_490, '#skF_4')=k5_relat_1(E_490, '#skF_4') | ~m1_subset_1(E_490, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))) | ~v1_funct_1(E_490))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10758])).
% 9.64/3.37  tff(c_11100, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_11091])).
% 9.64/3.37  tff(c_11108, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3055, c_11100])).
% 9.64/3.37  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.64/3.37  tff(c_11124, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11108, c_2])).
% 9.64/3.37  tff(c_11140, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_131, c_11124])).
% 9.64/3.37  tff(c_12896, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12890, c_11140])).
% 9.64/3.37  tff(c_12918, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11463, c_231, c_11283, c_12896])).
% 9.64/3.37  tff(c_26, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.64/3.37  tff(c_12958, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12918, c_26])).
% 9.64/3.37  tff(c_12979, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84, c_6517, c_12958])).
% 9.64/3.37  tff(c_12981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_12979])).
% 9.64/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.37  
% 9.64/3.37  Inference rules
% 9.64/3.37  ----------------------
% 9.64/3.37  #Ref     : 0
% 9.64/3.37  #Sup     : 2804
% 9.64/3.38  #Fact    : 0
% 9.64/3.38  #Define  : 0
% 9.64/3.38  #Split   : 33
% 9.64/3.38  #Chain   : 0
% 9.64/3.38  #Close   : 0
% 9.64/3.38  
% 9.64/3.38  Ordering : KBO
% 9.64/3.38  
% 9.64/3.38  Simplification rules
% 9.64/3.38  ----------------------
% 9.64/3.38  #Subsume      : 106
% 9.64/3.38  #Demod        : 4926
% 9.64/3.38  #Tautology    : 1304
% 9.64/3.38  #SimpNegUnit  : 59
% 9.64/3.38  #BackRed      : 62
% 9.64/3.38  
% 9.64/3.38  #Partial instantiations: 0
% 9.64/3.38  #Strategies tried      : 1
% 9.64/3.38  
% 9.64/3.38  Timing (in seconds)
% 9.64/3.38  ----------------------
% 9.64/3.38  Preprocessing        : 0.42
% 9.64/3.38  Parsing              : 0.22
% 9.64/3.38  CNF conversion       : 0.03
% 9.64/3.38  Main loop            : 2.15
% 9.64/3.38  Inferencing          : 0.67
% 9.64/3.38  Reduction            : 0.90
% 9.64/3.38  Demodulation         : 0.70
% 9.64/3.38  BG Simplification    : 0.09
% 9.64/3.38  Subsumption          : 0.37
% 9.64/3.38  Abstraction          : 0.11
% 9.64/3.38  MUC search           : 0.00
% 9.64/3.38  Cooper               : 0.00
% 9.64/3.38  Total                : 2.63
% 9.64/3.38  Index Insertion      : 0.00
% 9.64/3.38  Index Deletion       : 0.00
% 9.64/3.38  Index Matching       : 0.00
% 9.64/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
