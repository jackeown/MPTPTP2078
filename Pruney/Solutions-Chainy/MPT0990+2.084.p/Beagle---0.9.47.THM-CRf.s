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
% DateTime   : Thu Dec  3 10:13:08 EST 2020

% Result     : Theorem 6.61s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 802 expanded)
%              Number of leaves         :   42 ( 303 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (3547 expanded)
%              Number of equality atoms :   94 (1322 expanded)
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

tff(f_200,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_174,axiom,(
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

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_91,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_132,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_158,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_100,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_195,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_208,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_195])).

tff(c_2254,plain,(
    ! [B_171,C_172,A_173] :
      ( k6_partfun1(B_171) = k5_relat_1(k2_funct_1(C_172),C_172)
      | k1_xboole_0 = B_171
      | ~ v2_funct_1(C_172)
      | k2_relset_1(A_173,B_171,C_172) != B_171
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_171)))
      | ~ v1_funct_2(C_172,A_173,B_171)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2260,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2254])).

tff(c_2270,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_208,c_2260])).

tff(c_2271,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2270])).

tff(c_2286,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2271])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_38,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_77,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30])).

tff(c_185,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_192,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_77,c_185])).

tff(c_1621,plain,(
    ! [C_136,D_134,B_138,F_137,E_139,A_135] :
      ( m1_subset_1(k1_partfun1(A_135,B_138,C_136,D_134,E_139,F_137),k1_zfmisc_1(k2_zfmisc_1(A_135,D_134)))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(C_136,D_134)))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_135,B_138)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_536,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_544,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_536])).

tff(c_559,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_544])).

tff(c_589,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_1644,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1621,c_589])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1644])).

tff(c_1671,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_2862,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k2_relset_1(A_195,B_196,C_197) = B_196
      | ~ r2_relset_1(B_196,B_196,k1_partfun1(B_196,A_195,A_195,B_196,D_198,C_197),k6_partfun1(B_196))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_zfmisc_1(B_196,A_195)))
      | ~ v1_funct_2(D_198,B_196,A_195)
      | ~ v1_funct_1(D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_2(C_197,A_195,B_196)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2868,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_2862])).

tff(c_2872,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_192,c_208,c_2868])).

tff(c_2874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2286,c_2872])).

tff(c_2875,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2271])).

tff(c_2915,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2875])).

tff(c_14,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_3859,plain,(
    ! [C_233,A_235,D_234,B_236,E_232] :
      ( k1_xboole_0 = C_233
      | v2_funct_1(E_232)
      | k2_relset_1(A_235,B_236,D_234) != B_236
      | ~ v2_funct_1(k1_partfun1(A_235,B_236,B_236,C_233,D_234,E_232))
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(B_236,C_233)))
      | ~ v1_funct_2(E_232,B_236,C_233)
      | ~ v1_funct_1(E_232)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_2(D_234,A_235,B_236)
      | ~ v1_funct_1(D_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3865,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_3859])).

tff(c_3873,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_64,c_3865])).

tff(c_3875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2915,c_58,c_3873])).

tff(c_3877,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2875])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2876,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2271])).

tff(c_2877,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2876,c_208])).

tff(c_4018,plain,(
    ! [A_240,C_241,B_242] :
      ( k6_partfun1(A_240) = k5_relat_1(C_241,k2_funct_1(C_241))
      | k1_xboole_0 = B_242
      | ~ v2_funct_1(C_241)
      | k2_relset_1(A_240,B_242,C_241) != B_242
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_240,B_242)))
      | ~ v1_funct_2(C_241,A_240,B_242)
      | ~ v1_funct_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_4024,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4018])).

tff(c_4034,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2877,c_3877,c_4024])).

tff(c_4035,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4034])).

tff(c_12,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_236,plain,(
    ! [A_75,B_76,C_77] :
      ( k5_relat_1(k5_relat_1(A_75,B_76),C_77) = k5_relat_1(A_75,k5_relat_1(B_76,C_77))
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_258,plain,(
    ! [A_8,C_77] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_77)) = k5_relat_1(A_8,C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_236])).

tff(c_273,plain,(
    ! [A_8,C_77] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_77)) = k5_relat_1(A_8,C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_258])).

tff(c_4065,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_273])).

tff(c_4072,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_4035,c_4065])).

tff(c_4076,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4072])).

tff(c_4079,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_4076])).

tff(c_4083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_70,c_4079])).

tff(c_4085,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4072])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_100])).

tff(c_201,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_195])).

tff(c_207,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_201])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_partfun1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_212,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_80])).

tff(c_216,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_212])).

tff(c_170,plain,(
    ! [A_66] :
      ( k1_relat_1(k2_funct_1(A_66)) = k2_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5186,plain,(
    ! [A_275] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_275)),k2_funct_1(A_275)) = k2_funct_1(A_275)
      | ~ v1_relat_1(k2_funct_1(A_275))
      | ~ v2_funct_1(A_275)
      | ~ v1_funct_1(A_275)
      | ~ v1_relat_1(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_81])).

tff(c_5212,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2876,c_5186])).

tff(c_5236,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_70,c_3877,c_4085,c_5212])).

tff(c_2135,plain,(
    ! [F_163,D_159,A_162,C_164,B_160,E_161] :
      ( k1_partfun1(A_162,B_160,C_164,D_159,E_161,F_163) = k5_relat_1(E_161,F_163)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_164,D_159)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_160)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2141,plain,(
    ! [A_162,B_160,E_161] :
      ( k1_partfun1(A_162,B_160,'#skF_2','#skF_1',E_161,'#skF_4') = k5_relat_1(E_161,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_160)))
      | ~ v1_funct_1(E_161) ) ),
    inference(resolution,[status(thm)],[c_66,c_2135])).

tff(c_3928,plain,(
    ! [A_237,B_238,E_239] :
      ( k1_partfun1(A_237,B_238,'#skF_2','#skF_1',E_239,'#skF_4') = k5_relat_1(E_239,'#skF_4')
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(E_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2141])).

tff(c_3934,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3928])).

tff(c_3941,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1671,c_3934])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3960,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3941,c_2])).

tff(c_3972,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_113,c_3960])).

tff(c_5242,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5236,c_3972])).

tff(c_5258,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_216,c_4035,c_5242])).

tff(c_20,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5293,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5258,c_20])).

tff(c_5311,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_70,c_3877,c_5293])).

tff(c_5313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5311])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.61/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.32  
% 6.61/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.32  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.61/2.32  
% 6.61/2.32  %Foreground sorts:
% 6.61/2.32  
% 6.61/2.32  
% 6.61/2.32  %Background operators:
% 6.61/2.32  
% 6.61/2.32  
% 6.61/2.32  %Foreground operators:
% 6.61/2.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.61/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.61/2.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.61/2.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.61/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.61/2.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.61/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.61/2.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.61/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.61/2.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.61/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.61/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.61/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.61/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.61/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.61/2.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.61/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.61/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.61/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.61/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.61/2.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.61/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.61/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.61/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.61/2.32  
% 6.61/2.34  tff(f_200, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.61/2.34  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.61/2.34  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.61/2.34  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.61/2.34  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.61/2.34  tff(f_91, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.61/2.34  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.61/2.34  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.61/2.34  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.61/2.34  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.61/2.34  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 6.61/2.34  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.61/2.34  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 6.61/2.34  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.61/2.34  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 6.61/2.34  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.61/2.34  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.61/2.34  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.61/2.34  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_100, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.61/2.34  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_100])).
% 6.61/2.34  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_195, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.61/2.34  tff(c_208, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_195])).
% 6.61/2.34  tff(c_2254, plain, (![B_171, C_172, A_173]: (k6_partfun1(B_171)=k5_relat_1(k2_funct_1(C_172), C_172) | k1_xboole_0=B_171 | ~v2_funct_1(C_172) | k2_relset_1(A_173, B_171, C_172)!=B_171 | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_171))) | ~v1_funct_2(C_172, A_173, B_171) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.61/2.34  tff(c_2260, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2254])).
% 6.61/2.34  tff(c_2270, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_208, c_2260])).
% 6.61/2.34  tff(c_2271, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_2270])).
% 6.61/2.34  tff(c_2286, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2271])).
% 6.61/2.34  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_38, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.61/2.34  tff(c_30, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.61/2.34  tff(c_77, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30])).
% 6.61/2.34  tff(c_185, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.61/2.34  tff(c_192, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_77, c_185])).
% 6.61/2.34  tff(c_1621, plain, (![C_136, D_134, B_138, F_137, E_139, A_135]: (m1_subset_1(k1_partfun1(A_135, B_138, C_136, D_134, E_139, F_137), k1_zfmisc_1(k2_zfmisc_1(A_135, D_134))) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(C_136, D_134))) | ~v1_funct_1(F_137) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_135, B_138))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.61/2.34  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_536, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.61/2.34  tff(c_544, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_536])).
% 6.61/2.34  tff(c_559, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_544])).
% 6.61/2.34  tff(c_589, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_559])).
% 6.61/2.34  tff(c_1644, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1621, c_589])).
% 6.61/2.34  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1644])).
% 6.61/2.34  tff(c_1671, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_559])).
% 6.61/2.34  tff(c_2862, plain, (![A_195, B_196, C_197, D_198]: (k2_relset_1(A_195, B_196, C_197)=B_196 | ~r2_relset_1(B_196, B_196, k1_partfun1(B_196, A_195, A_195, B_196, D_198, C_197), k6_partfun1(B_196)) | ~m1_subset_1(D_198, k1_zfmisc_1(k2_zfmisc_1(B_196, A_195))) | ~v1_funct_2(D_198, B_196, A_195) | ~v1_funct_1(D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_2(C_197, A_195, B_196) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.61/2.34  tff(c_2868, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1671, c_2862])).
% 6.61/2.34  tff(c_2872, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_192, c_208, c_2868])).
% 6.61/2.34  tff(c_2874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2286, c_2872])).
% 6.61/2.34  tff(c_2875, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2271])).
% 6.61/2.34  tff(c_2915, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2875])).
% 6.61/2.34  tff(c_14, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.61/2.34  tff(c_78, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 6.61/2.34  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.61/2.34  tff(c_3859, plain, (![C_233, A_235, D_234, B_236, E_232]: (k1_xboole_0=C_233 | v2_funct_1(E_232) | k2_relset_1(A_235, B_236, D_234)!=B_236 | ~v2_funct_1(k1_partfun1(A_235, B_236, B_236, C_233, D_234, E_232)) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(B_236, C_233))) | ~v1_funct_2(E_232, B_236, C_233) | ~v1_funct_1(E_232) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_2(D_234, A_235, B_236) | ~v1_funct_1(D_234))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.61/2.34  tff(c_3865, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1671, c_3859])).
% 6.61/2.34  tff(c_3873, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_64, c_3865])).
% 6.61/2.34  tff(c_3875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2915, c_58, c_3873])).
% 6.61/2.34  tff(c_3877, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2875])).
% 6.61/2.34  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.61/2.34  tff(c_2876, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2271])).
% 6.61/2.34  tff(c_2877, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2876, c_208])).
% 6.61/2.34  tff(c_4018, plain, (![A_240, C_241, B_242]: (k6_partfun1(A_240)=k5_relat_1(C_241, k2_funct_1(C_241)) | k1_xboole_0=B_242 | ~v2_funct_1(C_241) | k2_relset_1(A_240, B_242, C_241)!=B_242 | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_240, B_242))) | ~v1_funct_2(C_241, A_240, B_242) | ~v1_funct_1(C_241))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.61/2.34  tff(c_4024, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4018])).
% 6.61/2.34  tff(c_4034, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2877, c_3877, c_4024])).
% 6.61/2.34  tff(c_4035, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_4034])).
% 6.61/2.34  tff(c_12, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.61/2.34  tff(c_79, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 6.61/2.34  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.61/2.34  tff(c_81, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 6.61/2.34  tff(c_236, plain, (![A_75, B_76, C_77]: (k5_relat_1(k5_relat_1(A_75, B_76), C_77)=k5_relat_1(A_75, k5_relat_1(B_76, C_77)) | ~v1_relat_1(C_77) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.34  tff(c_258, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_81, c_236])).
% 6.61/2.34  tff(c_273, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_258])).
% 6.61/2.34  tff(c_4065, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4035, c_273])).
% 6.61/2.34  tff(c_4072, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_4035, c_4065])).
% 6.61/2.34  tff(c_4076, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4072])).
% 6.61/2.34  tff(c_4079, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_4076])).
% 6.61/2.34  tff(c_4083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_70, c_4079])).
% 6.61/2.34  tff(c_4085, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4072])).
% 6.61/2.34  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_100])).
% 6.61/2.34  tff(c_201, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_195])).
% 6.61/2.34  tff(c_207, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_201])).
% 6.61/2.34  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.61/2.34  tff(c_80, plain, (![A_9]: (k5_relat_1(A_9, k6_partfun1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 6.61/2.34  tff(c_212, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_80])).
% 6.61/2.34  tff(c_216, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_212])).
% 6.61/2.34  tff(c_170, plain, (![A_66]: (k1_relat_1(k2_funct_1(A_66))=k2_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.61/2.34  tff(c_5186, plain, (![A_275]: (k5_relat_1(k6_partfun1(k2_relat_1(A_275)), k2_funct_1(A_275))=k2_funct_1(A_275) | ~v1_relat_1(k2_funct_1(A_275)) | ~v2_funct_1(A_275) | ~v1_funct_1(A_275) | ~v1_relat_1(A_275))), inference(superposition, [status(thm), theory('equality')], [c_170, c_81])).
% 6.61/2.34  tff(c_5212, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2876, c_5186])).
% 6.61/2.34  tff(c_5236, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_70, c_3877, c_4085, c_5212])).
% 6.61/2.35  tff(c_2135, plain, (![F_163, D_159, A_162, C_164, B_160, E_161]: (k1_partfun1(A_162, B_160, C_164, D_159, E_161, F_163)=k5_relat_1(E_161, F_163) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(C_164, D_159))) | ~v1_funct_1(F_163) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_160))) | ~v1_funct_1(E_161))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.61/2.35  tff(c_2141, plain, (![A_162, B_160, E_161]: (k1_partfun1(A_162, B_160, '#skF_2', '#skF_1', E_161, '#skF_4')=k5_relat_1(E_161, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_160))) | ~v1_funct_1(E_161))), inference(resolution, [status(thm)], [c_66, c_2135])).
% 6.61/2.35  tff(c_3928, plain, (![A_237, B_238, E_239]: (k1_partfun1(A_237, B_238, '#skF_2', '#skF_1', E_239, '#skF_4')=k5_relat_1(E_239, '#skF_4') | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_1(E_239))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2141])).
% 6.61/2.35  tff(c_3934, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3928])).
% 6.61/2.35  tff(c_3941, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1671, c_3934])).
% 6.61/2.35  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.35  tff(c_3960, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3941, c_2])).
% 6.61/2.35  tff(c_3972, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_113, c_3960])).
% 6.61/2.35  tff(c_5242, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5236, c_3972])).
% 6.61/2.35  tff(c_5258, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4085, c_216, c_4035, c_5242])).
% 6.61/2.35  tff(c_20, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.61/2.35  tff(c_5293, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5258, c_20])).
% 6.61/2.35  tff(c_5311, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_70, c_3877, c_5293])).
% 6.61/2.35  tff(c_5313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5311])).
% 6.61/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.35  
% 6.61/2.35  Inference rules
% 6.61/2.35  ----------------------
% 6.61/2.35  #Ref     : 0
% 6.61/2.35  #Sup     : 1162
% 6.61/2.35  #Fact    : 0
% 6.61/2.35  #Define  : 0
% 6.61/2.35  #Split   : 18
% 6.61/2.35  #Chain   : 0
% 6.61/2.35  #Close   : 0
% 6.61/2.35  
% 6.61/2.35  Ordering : KBO
% 6.61/2.35  
% 6.61/2.35  Simplification rules
% 6.61/2.35  ----------------------
% 6.61/2.35  #Subsume      : 27
% 6.61/2.35  #Demod        : 1639
% 6.61/2.35  #Tautology    : 518
% 6.61/2.35  #SimpNegUnit  : 50
% 6.61/2.35  #BackRed      : 17
% 6.61/2.35  
% 6.61/2.35  #Partial instantiations: 0
% 6.61/2.35  #Strategies tried      : 1
% 6.61/2.35  
% 6.61/2.35  Timing (in seconds)
% 6.61/2.35  ----------------------
% 6.61/2.35  Preprocessing        : 0.35
% 6.61/2.35  Parsing              : 0.18
% 6.61/2.35  CNF conversion       : 0.03
% 6.61/2.35  Main loop            : 1.16
% 6.61/2.35  Inferencing          : 0.40
% 6.61/2.35  Reduction            : 0.45
% 6.61/2.35  Demodulation         : 0.34
% 6.61/2.35  BG Simplification    : 0.05
% 6.61/2.35  Subsumption          : 0.20
% 6.61/2.35  Abstraction          : 0.06
% 6.61/2.35  MUC search           : 0.00
% 6.61/2.35  Cooper               : 0.00
% 6.61/2.35  Total                : 1.56
% 6.61/2.35  Index Insertion      : 0.00
% 6.61/2.35  Index Deletion       : 0.00
% 6.61/2.35  Index Matching       : 0.00
% 6.61/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
