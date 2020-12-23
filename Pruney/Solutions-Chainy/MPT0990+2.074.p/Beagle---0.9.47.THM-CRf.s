%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 6.58s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 788 expanded)
%              Number of leaves         :   43 ( 299 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (3537 expanded)
%              Number of equality atoms :   94 (1312 expanded)
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

tff(f_202,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_176,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_160,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_111,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_124,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_111])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_198,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_211,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_198])).

tff(c_1966,plain,(
    ! [B_164,C_165,A_166] :
      ( k6_partfun1(B_164) = k5_relat_1(k2_funct_1(C_165),C_165)
      | k1_xboole_0 = B_164
      | ~ v2_funct_1(C_165)
      | k2_relset_1(A_166,B_164,C_165) != B_164
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_164)))
      | ~ v1_funct_2(C_165,A_166,B_164)
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1972,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1966])).

tff(c_1982,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_211,c_1972])).

tff(c_1983,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1982])).

tff(c_1998,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1983])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_157,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_164,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_36,c_157])).

tff(c_1396,plain,(
    ! [C_128,B_129,A_132,E_130,D_133,F_131] :
      ( m1_subset_1(k1_partfun1(A_132,B_129,C_128,D_133,E_130,F_131),k1_zfmisc_1(k2_zfmisc_1(A_132,D_133)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_128,D_133)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_537,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_545,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_537])).

tff(c_560,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_545])).

tff(c_577,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_1416,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1396,c_577])).

tff(c_1441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1416])).

tff(c_1442,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_2586,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k2_relset_1(A_188,B_189,C_190) = B_189
      | ~ r2_relset_1(B_189,B_189,k1_partfun1(B_189,A_188,A_188,B_189,D_191,C_190),k6_partfun1(B_189))
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(B_189,A_188)))
      | ~ v1_funct_2(D_191,B_189,A_188)
      | ~ v1_funct_1(D_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_190,A_188,B_189)
      | ~ v1_funct_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2592,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_2586])).

tff(c_2596,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_164,c_211,c_2592])).

tff(c_2598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1998,c_2596])).

tff(c_2599,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1983])).

tff(c_2639,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2599])).

tff(c_40,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_3579,plain,(
    ! [D_227,C_226,A_228,B_229,E_225] :
      ( k1_xboole_0 = C_226
      | v2_funct_1(E_225)
      | k2_relset_1(A_228,B_229,D_227) != B_229
      | ~ v2_funct_1(k1_partfun1(A_228,B_229,B_229,C_226,D_227,E_225))
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(B_229,C_226)))
      | ~ v1_funct_2(E_225,B_229,C_226)
      | ~ v1_funct_1(E_225)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_2(D_227,A_228,B_229)
      | ~ v1_funct_1(D_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3585,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_3579])).

tff(c_3593,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_79,c_66,c_3585])).

tff(c_3595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2639,c_60,c_3593])).

tff(c_3597,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2599])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2600,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1983])).

tff(c_2601,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2600,c_211])).

tff(c_3733,plain,(
    ! [A_233,C_234,B_235] :
      ( k6_partfun1(A_233) = k5_relat_1(C_234,k2_funct_1(C_234))
      | k1_xboole_0 = B_235
      | ~ v2_funct_1(C_234)
      | k2_relset_1(A_233,B_235,C_234) != B_235
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_233,B_235)))
      | ~ v1_funct_2(C_234,A_233,B_235)
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3739,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3733])).

tff(c_3749,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2601,c_3597,c_3739])).

tff(c_3750,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3749])).

tff(c_12,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_229,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_82,c_229])).

tff(c_270,plain,(
    ! [A_8,C_77] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_77)) = k5_relat_1(A_8,C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_258])).

tff(c_3776,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3750,c_270])).

tff(c_3783,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3750,c_3776])).

tff(c_3787,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3783])).

tff(c_3790,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3787])).

tff(c_3794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_3790])).

tff(c_3796,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3783])).

tff(c_123,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_111])).

tff(c_204,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_198])).

tff(c_210,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_204])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_partfun1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_215,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_81])).

tff(c_219,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_215])).

tff(c_168,plain,(
    ! [A_70] :
      ( k1_relat_1(k2_funct_1(A_70)) = k2_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4700,plain,(
    ! [A_266] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_266)),k2_funct_1(A_266)) = k2_funct_1(A_266)
      | ~ v1_relat_1(k2_funct_1(A_266))
      | ~ v2_funct_1(A_266)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_82])).

tff(c_4726,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2600,c_4700])).

tff(c_4750,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_3597,c_3796,c_4726])).

tff(c_1920,plain,(
    ! [C_158,A_156,E_155,F_157,D_153,B_154] :
      ( k1_partfun1(A_156,B_154,C_158,D_153,E_155,F_157) = k5_relat_1(E_155,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_158,D_153)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1926,plain,(
    ! [A_156,B_154,E_155] :
      ( k1_partfun1(A_156,B_154,'#skF_2','#skF_1',E_155,'#skF_4') = k5_relat_1(E_155,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_155) ) ),
    inference(resolution,[status(thm)],[c_68,c_1920])).

tff(c_3648,plain,(
    ! [A_230,B_231,E_232] :
      ( k1_partfun1(A_230,B_231,'#skF_2','#skF_1',E_232,'#skF_4') = k5_relat_1(E_232,'#skF_4')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1926])).

tff(c_3654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3648])).

tff(c_3661,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1442,c_3654])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3677,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3661,c_2])).

tff(c_3687,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_124,c_3677])).

tff(c_4761,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4750,c_3687])).

tff(c_4777,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_219,c_3750,c_4761])).

tff(c_20,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4810,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4777,c_20])).

tff(c_4826,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_3597,c_4810])).

tff(c_4828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.58/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.36  
% 6.58/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.36  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.58/2.36  
% 6.58/2.36  %Foreground sorts:
% 6.58/2.36  
% 6.58/2.36  
% 6.58/2.36  %Background operators:
% 6.58/2.36  
% 6.58/2.36  
% 6.58/2.36  %Foreground operators:
% 6.58/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.58/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.58/2.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.58/2.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.58/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.58/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.58/2.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.58/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.58/2.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.58/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.58/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.58/2.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.58/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.58/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.58/2.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.58/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.58/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.58/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.58/2.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.58/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.58/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.58/2.36  
% 6.58/2.38  tff(f_202, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.58/2.38  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.58/2.38  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.58/2.38  tff(f_176, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.58/2.38  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.58/2.38  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.58/2.38  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.58/2.38  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.58/2.38  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.58/2.38  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.58/2.38  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.58/2.38  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.58/2.38  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.58/2.38  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.58/2.38  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.58/2.38  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.58/2.38  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.58/2.38  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.58/2.38  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_111, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.58/2.38  tff(c_124, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_111])).
% 6.58/2.38  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_198, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.58/2.38  tff(c_211, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_198])).
% 6.58/2.38  tff(c_1966, plain, (![B_164, C_165, A_166]: (k6_partfun1(B_164)=k5_relat_1(k2_funct_1(C_165), C_165) | k1_xboole_0=B_164 | ~v2_funct_1(C_165) | k2_relset_1(A_166, B_164, C_165)!=B_164 | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_164))) | ~v1_funct_2(C_165, A_166, B_164) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.58/2.38  tff(c_1972, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1966])).
% 6.58/2.38  tff(c_1982, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_211, c_1972])).
% 6.58/2.38  tff(c_1983, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_1982])).
% 6.58/2.38  tff(c_1998, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1983])).
% 6.58/2.38  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_36, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.58/2.38  tff(c_157, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.58/2.38  tff(c_164, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_36, c_157])).
% 6.58/2.38  tff(c_1396, plain, (![C_128, B_129, A_132, E_130, D_133, F_131]: (m1_subset_1(k1_partfun1(A_132, B_129, C_128, D_133, E_130, F_131), k1_zfmisc_1(k2_zfmisc_1(A_132, D_133))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_128, D_133))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_129))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.58/2.38  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_537, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.58/2.38  tff(c_545, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_537])).
% 6.58/2.38  tff(c_560, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_545])).
% 6.58/2.38  tff(c_577, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_560])).
% 6.58/2.38  tff(c_1416, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1396, c_577])).
% 6.58/2.38  tff(c_1441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1416])).
% 6.58/2.38  tff(c_1442, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_560])).
% 6.58/2.38  tff(c_2586, plain, (![A_188, B_189, C_190, D_191]: (k2_relset_1(A_188, B_189, C_190)=B_189 | ~r2_relset_1(B_189, B_189, k1_partfun1(B_189, A_188, A_188, B_189, D_191, C_190), k6_partfun1(B_189)) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(B_189, A_188))) | ~v1_funct_2(D_191, B_189, A_188) | ~v1_funct_1(D_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2(C_190, A_188, B_189) | ~v1_funct_1(C_190))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.58/2.38  tff(c_2592, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1442, c_2586])).
% 6.58/2.38  tff(c_2596, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_164, c_211, c_2592])).
% 6.58/2.38  tff(c_2598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1998, c_2596])).
% 6.58/2.38  tff(c_2599, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1983])).
% 6.58/2.38  tff(c_2639, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2599])).
% 6.58/2.38  tff(c_40, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.58/2.38  tff(c_14, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.58/2.38  tff(c_79, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 6.58/2.38  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.58/2.38  tff(c_3579, plain, (![D_227, C_226, A_228, B_229, E_225]: (k1_xboole_0=C_226 | v2_funct_1(E_225) | k2_relset_1(A_228, B_229, D_227)!=B_229 | ~v2_funct_1(k1_partfun1(A_228, B_229, B_229, C_226, D_227, E_225)) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(B_229, C_226))) | ~v1_funct_2(E_225, B_229, C_226) | ~v1_funct_1(E_225) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_2(D_227, A_228, B_229) | ~v1_funct_1(D_227))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.58/2.38  tff(c_3585, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1442, c_3579])).
% 6.58/2.38  tff(c_3593, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_79, c_66, c_3585])).
% 6.58/2.38  tff(c_3595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2639, c_60, c_3593])).
% 6.58/2.38  tff(c_3597, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2599])).
% 6.58/2.38  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.58/2.38  tff(c_2600, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1983])).
% 6.58/2.38  tff(c_2601, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2600, c_211])).
% 6.58/2.38  tff(c_3733, plain, (![A_233, C_234, B_235]: (k6_partfun1(A_233)=k5_relat_1(C_234, k2_funct_1(C_234)) | k1_xboole_0=B_235 | ~v2_funct_1(C_234) | k2_relset_1(A_233, B_235, C_234)!=B_235 | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_233, B_235))) | ~v1_funct_2(C_234, A_233, B_235) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.58/2.38  tff(c_3739, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3733])).
% 6.58/2.38  tff(c_3749, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2601, c_3597, c_3739])).
% 6.58/2.38  tff(c_3750, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_3749])).
% 6.58/2.38  tff(c_12, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.58/2.38  tff(c_80, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12])).
% 6.58/2.38  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.58/2.38  tff(c_82, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 6.58/2.38  tff(c_229, plain, (![A_75, B_76, C_77]: (k5_relat_1(k5_relat_1(A_75, B_76), C_77)=k5_relat_1(A_75, k5_relat_1(B_76, C_77)) | ~v1_relat_1(C_77) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.58/2.38  tff(c_258, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_82, c_229])).
% 6.58/2.38  tff(c_270, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_258])).
% 6.58/2.38  tff(c_3776, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3750, c_270])).
% 6.58/2.38  tff(c_3783, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3750, c_3776])).
% 6.58/2.38  tff(c_3787, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3783])).
% 6.58/2.38  tff(c_3790, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_3787])).
% 6.58/2.38  tff(c_3794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_3790])).
% 6.58/2.38  tff(c_3796, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3783])).
% 6.58/2.38  tff(c_123, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_111])).
% 6.58/2.38  tff(c_204, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_198])).
% 6.58/2.38  tff(c_210, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_204])).
% 6.58/2.38  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.58/2.38  tff(c_81, plain, (![A_9]: (k5_relat_1(A_9, k6_partfun1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6])).
% 6.58/2.38  tff(c_215, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_210, c_81])).
% 6.58/2.38  tff(c_219, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_215])).
% 6.58/2.38  tff(c_168, plain, (![A_70]: (k1_relat_1(k2_funct_1(A_70))=k2_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.38  tff(c_4700, plain, (![A_266]: (k5_relat_1(k6_partfun1(k2_relat_1(A_266)), k2_funct_1(A_266))=k2_funct_1(A_266) | ~v1_relat_1(k2_funct_1(A_266)) | ~v2_funct_1(A_266) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_168, c_82])).
% 6.58/2.38  tff(c_4726, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2600, c_4700])).
% 6.58/2.38  tff(c_4750, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_3597, c_3796, c_4726])).
% 6.58/2.38  tff(c_1920, plain, (![C_158, A_156, E_155, F_157, D_153, B_154]: (k1_partfun1(A_156, B_154, C_158, D_153, E_155, F_157)=k5_relat_1(E_155, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_158, D_153))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.58/2.38  tff(c_1926, plain, (![A_156, B_154, E_155]: (k1_partfun1(A_156, B_154, '#skF_2', '#skF_1', E_155, '#skF_4')=k5_relat_1(E_155, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_1(E_155))), inference(resolution, [status(thm)], [c_68, c_1920])).
% 6.58/2.38  tff(c_3648, plain, (![A_230, B_231, E_232]: (k1_partfun1(A_230, B_231, '#skF_2', '#skF_1', E_232, '#skF_4')=k5_relat_1(E_232, '#skF_4') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_1(E_232))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1926])).
% 6.58/2.38  tff(c_3654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3648])).
% 6.58/2.38  tff(c_3661, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1442, c_3654])).
% 6.58/2.38  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.58/2.38  tff(c_3677, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3661, c_2])).
% 6.58/2.38  tff(c_3687, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_124, c_3677])).
% 6.58/2.38  tff(c_4761, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4750, c_3687])).
% 6.58/2.38  tff(c_4777, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_219, c_3750, c_4761])).
% 6.58/2.38  tff(c_20, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.58/2.38  tff(c_4810, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4777, c_20])).
% 6.58/2.38  tff(c_4826, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_3597, c_4810])).
% 6.58/2.38  tff(c_4828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_4826])).
% 6.58/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.38  
% 6.58/2.38  Inference rules
% 6.58/2.38  ----------------------
% 6.58/2.38  #Ref     : 0
% 6.58/2.38  #Sup     : 1057
% 6.58/2.38  #Fact    : 0
% 6.58/2.38  #Define  : 0
% 6.58/2.38  #Split   : 18
% 6.58/2.38  #Chain   : 0
% 6.58/2.38  #Close   : 0
% 6.58/2.38  
% 6.58/2.38  Ordering : KBO
% 6.58/2.38  
% 6.58/2.38  Simplification rules
% 6.58/2.38  ----------------------
% 6.58/2.38  #Subsume      : 26
% 6.58/2.38  #Demod        : 1476
% 6.58/2.38  #Tautology    : 481
% 6.58/2.38  #SimpNegUnit  : 46
% 6.58/2.38  #BackRed      : 17
% 6.58/2.38  
% 6.58/2.38  #Partial instantiations: 0
% 6.58/2.38  #Strategies tried      : 1
% 6.58/2.38  
% 6.58/2.38  Timing (in seconds)
% 6.58/2.38  ----------------------
% 6.58/2.38  Preprocessing        : 0.39
% 6.58/2.38  Parsing              : 0.20
% 6.58/2.38  CNF conversion       : 0.03
% 6.58/2.38  Main loop            : 1.22
% 6.58/2.38  Inferencing          : 0.44
% 6.58/2.38  Reduction            : 0.45
% 6.58/2.38  Demodulation         : 0.34
% 6.58/2.38  BG Simplification    : 0.05
% 6.58/2.38  Subsumption          : 0.20
% 6.58/2.38  Abstraction          : 0.06
% 6.58/2.38  MUC search           : 0.00
% 6.58/2.38  Cooper               : 0.00
% 6.58/2.38  Total                : 1.65
% 6.58/2.38  Index Insertion      : 0.00
% 6.58/2.38  Index Deletion       : 0.00
% 6.58/2.39  Index Matching       : 0.00
% 6.58/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
